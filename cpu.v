`timescale 1ps/1ps

`define LAST 2

// Branch Prediction States
`define FF_ST 0
`define F_ST  1
`define T_ST  2
`define TT_ST 3


//
// This is an inefficient implementation.
//   make it run correctly in less cycles, fastest implementation wins
//

module main();

    // clock
    wire clk;
    clock c0(clk);

    reg [15:0] cycle = 0;

    wire [15:0] inst;

    reg [15:0]f_inst = 16'hffff;
    reg [15:0]d_inst = 16'hffff;
    reg [15:0]r0_inst = 16'hffff;
    reg [15:0]r1_inst = 16'hffff;
    reg [15:0]x_inst = 16'hffff;
    reg [15:0]l0_inst = 16'hffff;
    reg [15:0]l1_inst = 16'hffff;
    reg [15:0]w_inst = 16'hffff;

    wire f_valid_inst = f_inst[15:12] <= 4'b0111;
    wire d_valid_inst = d_inst[15:12] <= 4'b0111;
    wire r0_valid_inst = r0_inst[15:12] <= 4'b0111;
    wire r1_valid_inst = r1_inst[15:12] <= 4'b0111;
    wire x_valid_inst = x_inst[15:12] <= 4'b0111;
    wire l0_valid_inst = l0_inst[15:12] <= 4'b0111;
    wire l1_valid_inst = l1_inst[15:12] <= 4'b0111;
    wire w_valid_inst = w_inst[15:12] <= 4'b0111;

    reg [15:0]pc = 16'h0000;
    reg [15:0]pc_no_jump = 16'h0000;
    reg [15:0]f_pc = 16'h0000;
    reg [15:0]d_pc;
    reg [15:0]r0_pc;
    reg [15:0]r1_pc;
    reg [15:0]x_pc;
    reg [15:0]l0_pc;
    reg [15:0]l1_pc;
    reg [15:0]w_pc;

    reg [15:0]busy = 16'h0000;

    reg [31:0]last_was_jump = 0;
    reg [31:0]last_was_cont = 0;
    //reg [31:0]history = 0;
    reg [31:0]predictor_v = 0;
    reg [31:0]predictor_right = 0;
    reg [31:0]predictor_wrong = 0;

    wire d_uses_rt = d_inst[15:12] == 4'b0000
                        | d_inst[15:12] == 4'b0001
                        | d_inst[15:12] == 4'b0100
                        | d_inst[15:12] == 4'b0101;
    wire d_uses_ra = d_inst[15:12] == 4'b0001
                        | d_inst[15:12] == 4'b0101
                        | d_inst[15:12] == 4'b0110
                        | d_inst[15:12] == 4'b0111;
    wire d_uses_rb = d_inst[15:12] == 4'b0001
                        | d_inst[15:12] == 4'b0101
                        | d_inst[15:12] == 4'b0110;

    wire d_is_jump = d_inst[15:12] == 4'b0010;

    wire d_is_x_jmp = d_inst[15:12] == 4'b0110;

    wire x_is_add = x_inst[15:12] == 4'b0001
                        | x_inst[15:12] == 4'b0101;
    wire x_is_jump = x_inst[15:12] == 4'b0110;

    wire w_uses_rt = w_inst[15:12] == 4'b0000
                        | w_inst[15:12] == 4'b0001
                        | w_inst[15:12] == 4'b0100
                        | w_inst[15:12] == 4'b0101;
    wire w_uses_ra = w_inst[15:12] == 4'b0001
                        | w_inst[15:12] == 4'b0101
                        | w_inst[15:12] == 4'b0110
                        | w_inst[15:12] == 4'b0111;
    wire w_uses_rb = w_inst[15:12] == 4'b0001
                        | w_inst[15:12] == 4'b0101
                        | w_inst[15:12] == 4'b0110;

    // TODO: determine stall here. If so, set correct_pc to
    // f_pc I think and set stall_ctr to 3(?)
    // check r0, r1, x
    
    wire d_is_mem = d_inst[15:12] == 4'b0100;
    wire d_is_st = d_inst[15:12] == 4'b0111;

    wire r0_is_st = r0_inst[15:12] == 4'b0111;

    wire r1_is_st = r1_inst[15:12] == 4'b0111;

    wire x_is_mem = x_inst[15:12] == 4'b0100
                        | l0_inst[15:12] == 4'b0101;
    wire x_is_st = x_inst[15:12] == 4'b0111;

    wire l0_is_st = l0_inst[15:12] == 4'b0101;
    wire l1_is_st = l1_inst[15:12] == 4'b0101;

    reg [2:0] stall_ctr = 0;
    reg [15:0] correct_pc = 16'hffff;

    wire reg_stall = (d_uses_ra && busy[d_ra])
                        || (d_uses_rb && busy[d_rb])
                        || (d_uses_rt && busy[d_rt]);

    wire pc_mem_stall = ((f_pc == d_s && d_is_st)
                        || (f_pc == r0_s && r0_is_st)
                        || (f_pc == r1_s && r1_is_st)
                        || (f_pc == x_s && x_is_st)
                        || (f_pc == l0_s && l0_is_st)
                        || (f_pc == l1_s && l1_is_st));

    wire d_mem_stall = (d_is_mem &&
                        (d_s == r0_s
                        || d_s == r1_s
                        || d_s == x_s));
    wire x_mem_stall = (x_is_mem &&
                        (x_s == l0_s
                        || x_s == l1_s));
    wire f_stall = reg_stall
                    | pc_mem_stall
                    | d_mem_stall
                    | x_mem_stall
                    | (stall_ctr > 0);

    wire d_stall = reg_stall
                    | d_mem_stall 
                    | x_mem_stall 
                    | (stall_ctr > 0);

    reg r0_stall = 0;
    reg r1_stall = 0;
    reg x_stall = 0;
    reg l0_stall = 0;
    reg l1_stall = 0;
    reg w_stall = 0;

    wire x_jmp_v = x_is_jump && (va == vb);

    reg[1:0] jmp_stall_ctr = 0;

    wire d_halt = (d_inst[15:12] == 4'b0011);

    reg r0_halt = 0;
    reg r1_halt = 0;
    reg x_halt = 0;
    reg l0_halt = 0;
    reg l1_halt = 0;
    reg w_halt = 0;

    // wire f_v = !stall & inst_valid & f_valid_inst;
    wire f_v = !f_stall & f_valid_inst & (cycle > 2);
    wire d_v = !d_stall & !x_jmp_v & d_valid_inst;
    wire r0_v = !r0_stall &
        !x_jmp_v & !x_mem_stall & r0_valid_inst;
    wire r1_v = !r1_stall &
        !x_jmp_v & !x_mem_stall & r1_valid_inst;
    wire x_v = !x_stall & !x_mem_stall & x_valid_inst;
    wire l0_v = !l0_stall & l0_valid_inst;
    wire l1_v = !l1_stall & l1_valid_inst;
    wire w_v = !w_stall & w_valid_inst;

    wire wen = (w_v
                & !w_stall
                & (w_inst[15:12] == 4'b0000
                    || w_inst[15:12] == 4'b0001
                    || w_inst[15:12] == 4'b0101
                    || w_inst[15:12] == 4'b0100));

    wire [3:0]d_ra = d_inst[11:8];
    wire [3:0]d_rb = d_inst[7:4];
    wire [3:0]d_rt = d_inst[3:0];

    wire [3:0]r0_ra = r0_inst[11:8];
    wire [3:0]r0_rb = r0_inst[7:4];
    wire [3:0]r0_rt = r0_inst[3:0];

    wire [3:0]r1_ra = r1_inst[11:8];
    wire [3:0]r1_rb = r1_inst[7:4];
    wire [3:0]r1_rt = r0_inst[3:0];

    wire [3:0]x_ra = x_inst[11:8];
    wire [3:0]x_rb = x_inst[7:4];

    wire [3:0]w_ra = w_inst[11:8];
    wire [3:0]w_rb = w_inst[7:4];
    wire [3:0]w_rt = w_inst[3:0];

    wire [15:0]va;
    wire [15:0]vb;

    wire [15:0]d_jjj = d_inst[11:0];

    wire [15:0]d_ii = d_inst[11:4];
    wire [15:0]r0_ii = r0_inst[11:4];
    wire [15:0]r1_ii = r1_inst[11:4];
    wire [15:0]x_ii = x_inst[11:4];
    wire [15:0]l0_ii = l0_inst[11:4];
    wire [15:0]l1_ii = l1_inst[11:4];

    wire [15:0]d_s = d_inst[7:0];
    wire [15:0]r0_s = r0_inst[7:0];
    wire [15:0]r1_s = r1_inst[7:0];
    wire [15:0]x_s = x_inst[7:0];
    wire [15:0]l0_s = l0_inst[7:0];
    wire [15:0]l1_s = l1_inst[7:0];

    wire [15:0]x_d = x_inst[3:0];

    reg [15:0]x_res; // what to write in the register file
    reg [15:0]l0_res;
    reg [15:0]l1_res;

    wire [15:0]w_res = (w_inst[15:12] == 4'b0000 || w_inst[15:12] == 4'b0001) ? l1_res : memData;

    // what to write in the register file
    wire [15:0]memIn = x_res;
    wire [15:0]memData;

    mem i0(clk,
        pc,inst,
        memIn,memData,
        (l0_inst[15:12] == 4'b0111), l0_s, x_res);

    wire ren = (r0_inst[15:12] == 4'b0001
                    || r0_inst[15:12] == 4'b0101
                    || r0_inst[15:12] == 4'b0110
                    || r0_inst[15:12] == 4'b0111);

    // global pattern 
    reg [7:0]jmp_pattern = 0;
    reg [7:0] history = 0;

    // Local State Machine
    reg [1:0]local_states[0:7];

    // Meta Predictor
    // 3
    reg [1:0]meta_predictor[0:7];

    wire d_global_predictor = (meta_predictor[d_pc%8]  == 3); 

    // registers
    regs rf(clk,
        ren, r0_ra, va,
        ren, r0_rb, vb, 
        wen, w_rt, w_res);

    counter ctr(w_halt,clk,f_v,);

    initial begin
        $dumpfile("cpu.vcd");
        $dumpvars(1,main);

        local_states[0] = 0;
        local_states[1] = 0;
        local_states[2] = 0;
        local_states[3] = 0;
        local_states[4] = 0;
        local_states[5] = 0;
        local_states[6] = 0;
        local_states[7] = 0;

        meta_predictor[0] = 0;
        meta_predictor[1] = 0;
        meta_predictor[2] = 0;
        meta_predictor[3] = 0;
        meta_predictor[4] = 0;
        meta_predictor[5] = 0;
        meta_predictor[6] = 0;
        meta_predictor[7] = 0;
    end

    always @(posedge clk) begin
        pc <= pc + 1;

        r0_stall <= d_stall;
        r1_stall <= r0_stall;
        x_stall <= r1_stall;
        l0_stall <= x_stall;
        l1_stall <= l0_stall;
        w_stall <= l1_stall;

        r0_halt <= d_halt;
        r1_halt <= r0_halt;
        x_halt <= r1_halt;
        l0_halt <= x_halt;
        l1_halt <= l0_halt;
        w_halt <= l1_halt;

        if (f_stall | d_stall) begin
            stall_ctr <= stall_ctr - 1;
            if (stall_ctr == 0) begin
                f_inst <= 16'hffff;
                if (reg_stall) begin
                    stall_ctr <= 5;
                end
                else if (pc_mem_stall) begin
                    stall_ctr <= 6;
                    d_inst <= 16'hffff;
                end
                else if (d_mem_stall) begin
                    stall_ctr <= 3;
                    pc <= correct_pc;
                end
                else if (x_mem_stall) begin
                    stall_ctr <= 3;
                    pc <= correct_pc;
                end
                correct_pc <= f_pc;
            end
            if (stall_ctr > 0) begin
                if (stall_ctr == 4) begin
                    pc <= correct_pc;
                end
                if (stall_ctr < 4) begin
                    f_inst <= inst;
                    f_pc <= pc > 1 ? (pc - 2) : 0;
                end
            end
        end
        else begin
            f_inst <= inst;
            f_pc <= pc > 1 ? (pc - 2) : 0;
        end

        if (f_v) begin
            d_inst <= f_inst;
            d_pc <= f_pc;
            // f_pc <= f_pc + 1;
        end

        if (d_v) begin
            r0_pc <= d_pc;
            r0_inst <= d_inst;
            if (d_uses_ra) begin
                busy[d_ra] <= 1;
            end
            if (d_uses_rb) begin
                busy[d_rb] <= 1;
            end
            if (d_uses_rt) begin
                busy[d_rt] <= 1;
            end
            if (d_is_jump) begin
                pc <= d_jjj;

                f_inst <= 16'hffff;
                d_inst <= 16'hffff;
                r0_inst <= 16'hffff;
                r1_inst <= 16'hffff;

                stall_ctr <= 3;
                //stall_ctr <= 0;
            end
            if (d_is_x_jmp) begin
                // if(local_states[d_pc%8] > `F_ST) begin
                //          
                // end
                if ((d_global_predictor) ? jmp_pattern[history] : local_states[d_pc%8] > `F_ST) begin
                // if ((history[d_pc%32] & last_was_jump[d_pc%32])
                //     | (~history[d_pc%32] & last_was_cont[d_pc%32])) begin
                    f_inst <= 16'hffff;
                    d_inst <= 16'hffff;

                    pc_no_jump <= d_pc + 1;
                    pc <= d_pc + d_inst[3:0];
                    stall_ctr <= 3;
                end
            end
        end
        else begin
            r0_inst <= 16'hffff;
        end

        if (r0_v) begin
            r1_pc <= r0_pc;
            r1_inst <= r0_inst;
        end
        else begin
            r1_inst <= 16'hffff;
        end

        if (r1_v) begin
            x_pc <= r1_pc;
            x_inst <= r1_inst;
        end
        else begin
            x_inst <= 16'hffff;
        end

        if (x_v) begin
            l0_pc <= x_pc;
            l0_inst <= x_inst;
            if (x_is_add) begin
                x_res <= va + vb;
            end
            else if (x_jmp_v) begin
                // we thought we weren't jumping but we are,
                // so we need to do this shit ya know
                // we should have already jumped so only need to do this
                // if we predicted wrong
                // history[x_pc%32] <= 1;
                history <= (history << 1) & 1'b1;
                // if (predictor_v[x_pc % 32]
                //     & ((history[x_pc%32] & ~last_was_jump[x_pc%32])
                //         | (~history[x_pc%32] & ~last_was_cont[x_pc%32]))) begin
                local_states[x_pc%8] <=
                    local_states[x_pc%8]
                    + ((local_states[x_pc%8] == 3) ? 0 : 1);
                if (~jmp_pattern[history] | local_states[x_pc%8] < 2) begin
                    // guessed wrong
                    $display("guessed wrong\n");
                    predictor_wrong <= predictor_wrong + 1;

                    jmp_pattern[history] <= 0;

                    pc <= x_pc + x_d;

                    r0_halt <= 0;
                    r1_halt <= 0;
                    x_halt <= 0;
                    l0_halt <= 0;
                    l1_halt <= 0;

                    f_inst <= 16'hffff;
                    d_inst <= 16'hffff;
                    r0_inst <= 16'hffff;
                    r1_inst <= 16'hffff;
                    x_inst <= 16'hffff;
                    l0_inst <= 16'hffff;

                    busy[r0_ra] <= 0;
                    busy[r0_rb] <= 0;
                    busy[r0_rt] <= 0;

                    busy[r1_ra] <= 0;
                    busy[r1_rb] <= 0;
                    busy[r1_rt] <= 0;

                    busy[x_ra] <= 0;
                    busy[x_rb] <= 0;

                    stall_ctr <= 3;
                end
                else begin
                    $display("guessed right\n");
                    predictor_right <= predictor_right + 1;
                end
            end
            else if (x_is_jump) begin
                // we jumped but we shouldn't have
                history <= (history << 1) & 1'b0;
                local_states[x_pc%8] <=
                    local_states[x_pc%8]
                    - ((local_states[x_pc%8] == 0) ? 0 : 1);
                if (jmp_pattern[history] | local_states[x_pc%8] >= 2) begin
                // if (predictor_v[x_pc % 32]
                //     & ((history[x_pc%32] & last_was_jump[x_pc%32])
                //         | (~history[x_pc%32] & last_was_cont[x_pc%32]))) begin
                //
                    jmp_pattern[history] <= 0;

                    $display("guessed wrong\n");
                    predictor_wrong <= predictor_wrong + 1;

                    pc <= pc_no_jump;

                    f_inst <= 16'hffff;
                    d_inst <= 16'hffff;
                    r0_inst <= 16'hffff;
                    r1_inst <= 16'hffff;
                    x_inst <= 16'hffff;

                    busy[r0_ra] <= 0;
                    busy[r0_rb] <= 0;
                    busy[r0_rt] <= 0;

                    busy[r1_ra] <= 0;
                    busy[r1_rb] <= 0;
                    busy[r1_rt] <= 0;

                    busy[x_ra] <= 0;
                    busy[x_rb] <= 0;

                    stall_ctr <= 3;
                end
                else begin
                    $display("guessed right\n");
                    predictor_right <= predictor_right + 1;
                end
            end
            else if (x_is_st) begin
                x_res <= va;
            end
            else begin
                x_res <= x_ii;
            end
        end
        else begin
            l0_inst <= 16'hffff;
        end

        if (l0_v) begin
            l1_pc <= l0_pc;
            l1_inst <= l0_inst;
            l0_res <= x_res;
        end
        else begin
            l1_inst <= 16'hffff;
        end

        if (l1_v) begin
            w_pc <= l1_pc;
            w_inst <= l1_inst;
            l1_res <= l0_res;
        end
        else begin
            w_inst <= 16'hffff;
        end

        if (w_v) begin
            //w_inst <= l_inst;
            if (w_halt) begin
                $display("%d / %d\n", predictor_right, (predictor_right + predictor_wrong));
            end
            if (w_uses_ra) begin
                busy[w_ra] <= 0;
            end
            if (w_uses_rb) begin
                busy[w_rb] <= 0;
            end
            if (w_uses_rt) begin
                busy[w_rt] <= 0;
            end
        end
        cycle <= cycle + 1;
    end

endmodule
