pragma circom 2.0.0;

/////////////////////////////////////////////////////////////////////////////////////
/////////////////////// Templates from the circomlib ////////////////////////////////
////////////////// Copy-pasted here for easy reference //////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

/*
 * Outputs `a` AND `b`
 */
template AND() {
    signal input a;
    signal input b;
    signal output out;

    out <== a*b;
}

/*
 * Outputs `a` OR `b`
 */
template OR() {
    signal input a;
    signal input b;
    signal output out;

    out <== a + b - a*b;
}

/*
 * `out` = `cond` ? `L` : `R`
 */
template IfThenElse() {
    signal input cond;
    signal input L;
    signal input R;
    signal output out;

    out <== cond * (L - R) + R;
}

/*
 * (`outL`, `outR`) = `sel` ? (`R`, `L`) : (`L`, `R`)
 */
template Switcher() {
    signal input sel;
    signal input L;
    signal input R;
    signal output outL;
    signal output outR;

    signal aux;

    aux <== (R-L)*sel;
    outL <==  aux + L;
    outR <== -aux + R;
}

/*
 * Decomposes `in` into `b` bits, given by `bits`.
 * Least significant bit in `bits[0]`.
 * Enforces that `in` is at most `b` bits long.
 */
template Num2Bits(b) {
    signal input in;
    signal output bits[b];

    for (var i = 0; i < b; i++) {
        bits[i] <-- (in >> i) & 1;
        bits[i] * (1 - bits[i]) === 0;
    }
    var sum_of_bits = 0;
    for (var i = 0; i < b; i++) {
        sum_of_bits += (2 ** i) * bits[i];
    }
    sum_of_bits === in;
}

/*
 * Reconstructs `out` from `b` bits, given by `bits`.
 * Least significant bit in `bits[0]`.
 */
template Bits2Num(b) {
    signal input bits[b];
    signal output out;
    var lc = 0;

    for (var i = 0; i < b; i++) {
        lc += (bits[i] * (1 << i));
    }
    out <== lc;
}

/*
 * Checks if `in` is zero and returns the output in `out`.
 */
template IsZero() {
    signal input in;
    signal output out;

    signal inv;

    inv <-- in!=0 ? 1/in : 0;

    out <== -in*inv +1;
    in*out === 0;
}

/*
 * Checks if `in[0]` == `in[1]` and returns the output in `out`.
 */
template IsEqual() {
    signal input in[2];
    signal output out;

    component isz = IsZero();

    in[1] - in[0] ==> isz.in;

    isz.out ==> out;
}

/*
 * Checks if `in[0]` < `in[1]` and returns the output in `out`.
 */
template LessThan(n) {
    assert(n <= 252);
    signal input in[2];
    signal output out;

    component n2b = Num2Bits(n+1);

    n2b.in <== in[0]+ (1<<n) - in[1];

    out <== 1-n2b.bits[n];
}

/////////////////////////////////////////////////////////////////////////////////////
///////////////////////// Templates for this lab ////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

/*
 * Outputs `out` = 1 if `in` is at most `b` bits long, and 0 otherwise.
 */
template CheckBitLength(b) {
    signal input in;
    signal output out;

    // TODO
    signal ins[b+1];
    signal rs[b+1];
    signal qs[b+1];
    ins[0] <== in;
    for (var i = 0; i < b; i++) {
        qs[i] <-- ins[i] \ 2;
        ins[i+1] <== qs[i];
        rs[i] <--ins[i] % 2;
        rs[i] * (1 - rs[i]) === 0;
        ins[i] === ins[i+1] * 2 + rs[i];
    }
    
    component ie = IsZero();
    ie.in <== ins[b];
    ie.out ==> out;
}

/*
 * Enforces the well-formedness of an exponent-mantissa pair (e, m), which is defined as follows:
 * if `e` is zero, then `m` must be zero
 * else, `e` must be at most `k` bits long, and `m` must be in the range [2^p, 2^p+1)
 */
template CheckWellFormedness(k, p) {
    signal input e;
    signal input m;

    // check if `e` is zero
    component is_e_zero = IsZero();
    is_e_zero.in <== e;

    // Case I: `e` is zero
    //// `m` must be zero
    component is_m_zero = IsZero();
    is_m_zero.in <== m;

    // Case II: `e` is nonzero
    //// `e` is `k` bits
    component check_e_bits = CheckBitLength(k);
    check_e_bits.in <== e;
    //// `m` is `p`+1 bits with the MSB equal to 1
    //// equivalent to check `m` - 2^`p` is in `p` bits
    component check_m_bits = CheckBitLength(p);
    check_m_bits.in <== m - (1 << p);

    // choose the right checks based on `is_e_zero`
    component if_else = IfThenElse();
    if_else.cond <== is_e_zero.out;
    if_else.L <== is_m_zero.out;
    //// check_m_bits.out * check_e_bits.out is equivalent to check_m_bits.out AND check_e_bits.out
    if_else.R <== check_m_bits.out * check_e_bits.out;

    // assert that those checks passed
    if_else.out === 1;
}

/*
 * Right-shifts `x` by `shift` bits to output `y`, where `shift` is a public circuit parameter.
 */
template RightShift(shift) {
    signal input x;
    signal output y;

    // TODO
    signal rs[shift+1];
    signal qs[shift+1];
    signal xs[shift+1];

    xs[0] <== x;
    for (var i = 0; i < shift; i++) {
        rs[i] <-- xs[i] % 2;
        rs[i] * (1 - rs[i]) === 0;
        qs[i] <-- xs[i] \ 2;
        xs[i+1] <== qs[i];
        xs[i] === xs[i+1] * 2 + rs[i];
    }

    y <== xs[shift];
}

/*
 * Rounds the input floating-point number and checks to ensure that rounding does not make the mantissa unnormalized.
 * Rounding is necessary to prevent the bitlength of the mantissa from growing with each successive operation.
 * The input is a normalized floating-point number (e, m) with precision `P`, where `e` is a `k`-bit exponent and `m` is a `P`+1-bit mantissa.
 * The output is a normalized floating-point number (e_out, m_out) representing the same value with a lower precision `p`.
 */
template RoundAndCheck(k, p, P) {
    signal input e;
    signal input m;
    signal output e_out;
    signal output m_out;
    assert(P > p);

    // check if no overflow occurs
    component if_no_overflow = LessThan(P+1);
    if_no_overflow.in[0] <== m;
    if_no_overflow.in[1] <== (1 << (P+1)) - (1 << (P-p-1));
    signal no_overflow <== if_no_overflow.out;

    var round_amt = P-p;
    // Case I: no overflow
    // compute (m + 2^{round_amt-1}) >> round_amt
    var m_prime = m + (1 << (round_amt-1));
    component right_shift = RightShift(round_amt);
    right_shift.x <== m_prime;
    var m_out_1 = right_shift.y;
    var e_out_1 = e;

    // Case II: overflow
    var e_out_2 = e + 1;
    var m_out_2 = (1 << p);

    // select right output based on no_overflow
    component if_else[2];
    for (var i = 0; i < 2; i++) {
        if_else[i] = IfThenElse();
        if_else[i].cond <== no_overflow;
    }
    if_else[0].L <== e_out_1;
    if_else[0].R <== e_out_2;
    if_else[1].L <== m_out_1;
    if_else[1].R <== m_out_2;
    e_out <== if_else[0].out;
    m_out <== if_else[1].out;
}

/*
 * Left-shifts `x` by `shift` bits to output `y`.
 * Enforces 0 <= `shift` < `shift_bound`.
 * If `skip_checks` = 1, then we don't care about the output and the `shift_bound` constraint is not enforced.
 */
template LeftShift(shift_bound) {
    signal input x;
    signal input shift;
    signal input skip_checks;
    signal output y;

    // TODO
    component lt = LessThan(10); // Potential bug
    lt.in[0] <== shift;
    lt.in[1] <== shift_bound;
    0 === (skip_checks - 1) * (lt.out - 1);

    signal multiplier;
    multiplier <-- 1 << shift;
    y <== x * multiplier;
}

/*
 * Find the Most-Significant Non-Zero Bit (MSNZB) of `in`, where `in` is assumed to be non-zero value of `b` bits.
 * Outputs the MSNZB as a one-hot vector `one_hot` of `b` bits, where `one_hot`[i] = 1 if MSNZB(`in`) = i and 0 otherwise.
 * The MSNZB is output as a one-hot vector to reduce the number of constraints in the subsequent `Normalize` template.
 * Enforces that `in` is non-zero as MSNZB(0) is undefined.
 * If `skip_checks` = 1, then we don't care about the output and the non-zero constraint is not enforced.
 */
template MSNZB(b) {
    signal input in;
    signal input skip_checks;
    signal output one_hot[b];

    // TODO
    component iz = IsZero();
    iz.in <== in;
    0 === (1 - skip_checks) * iz.out;

    component check_bit_length = CheckBitLength(b);
    check_bit_length.in <== in;
    check_bit_length.out === 1;

    component n2b = Num2Bits(b);
    n2b.in <== in;

    signal prefix_or[b];
    signal q[b];
    one_hot[b - 1] <== n2b.bits[b - 1];
    prefix_or[b - 1] <== n2b.bits[b - 1];

    for (var i = b - 2; i >= 0; i--) {
        q[i] <-- prefix_or[i + 1] | n2b.bits[i];
        prefix_or[i] <== q[i];
        one_hot[i] <== n2b.bits[i] * (1 - prefix_or[i + 1]);
    }
}

/*
 * Normalizes the input floating-point number.
 * The input is a floating-point number with a `k`-bit exponent `e` and a `P`+1-bit *unnormalized* mantissa `m` with precision `p`, where `m` is assumed to be non-zero.
 * The output is a floating-point number representing the same value with exponent `e_out` and a *normalized* mantissa `m_out` of `P`+1-bits and precision `P`.
 * Enforces that `m` is non-zero as a zero-value can not be normalized.
 * If `skip_checks` = 1, then we don't care about the output and the non-zero constraint is not enforced.
 */
template Normalize(k, p, P) {
    signal input e;
    signal input m;
    signal input skip_checks;
    signal output e_out;
    signal output m_out;
    assert(P > p);

    // TODO
    component iz = IsZero();
    iz.in <== m;
    0 === (1 - skip_checks) * iz.out;

    component msnzb = MSNZB(P + 1);
    msnzb.in <== m;
    msnzb.skip_checks <== skip_checks;

    signal ell[P + 1];
    ell[0] <== 0;
    for (var i = 1; i < P + 1; i++) {
        ell[i] <== ell[i - 1] + i * msnzb.one_hot[i];
    }

    component ls = LeftShift(P);
    ls.x <== m;
    ls.shift <== P - ell[P];
    ls.skip_checks <== skip_checks;

    m_out <== ls.y;
    e_out <== e + ell[P] - p;
}

/*
 * Adds two floating-point numbers.
 * The inputs are normalized floating-point numbers with `k`-bit exponents `e` and `p`+1-bit mantissas `m` with scale `p`.
 * Does not assume that the inputs are well-formed and makes appropriate checks for the same.
 * The output is a normalized floating-point number with exponent `e_out` and mantissa `m_out` of `p`+1-bits and scale `p`.
 * Enforces that inputs are well-formed.
 */
template FloatAdd(k, p) {
    signal input e[2];
    signal input m[2];
    signal output e_out;
    signal output m_out;

    // TODO
    component cwf[2];
    for (var i = 0; i < 2; i++) {
        cwf[i] = CheckWellFormedness(k, p);
        cwf[i].e <== e[i];
        cwf[i].m <== m[i];
    }

    signal mgn[2];
    component ls[2];
    for (var i = 0; i < 2; i++) {
        ls[i] = LeftShift(p + 2);
        ls[i].x <== e[i];
        ls[i].shift <== p + 1;
        ls[i].skip_checks <== 1;
        mgn[i] <== ls[i].y + m[i];
    }

    signal alpha_e;
    signal alpha_m;
    signal beta_e;
    signal beta_m;

    component lt1; // if mgn_1 > mgn_2:
    lt1 = LessThan(p + k + 1);
    lt1.in[0] <== mgn[1];
    lt1.in[1] <== mgn[0];

    component switcher[2];
    switcher[0] = Switcher();
    switcher[0].sel <== lt1.out;
    switcher[0].L <== e[1];
    switcher[0].R <== e[0];
    alpha_e <== switcher[0].outL;
    beta_e <== switcher[0].outR;

    switcher[1] = Switcher();
    switcher[1].sel <== lt1.out;
    switcher[1].L <== m[1];
    switcher[1].R <== m[0];
    alpha_m <== switcher[1].outL;
    beta_m <== switcher[1].outR;

    signal diff <== alpha_e - beta_e;

    component or = OR();
    component lt2 = LessThan(k + 1); // e ~ 2 ^ k
    lt2.in[0] <== p + 1;
    lt2.in[1] <== diff;
    component iz2 = IsZero();
    iz2.in <== alpha_e;

    or.a <== lt2.out;
    or.b <== iz2.out;
    signal condition <== or.out;

    component ls1 = LeftShift(0);
    ls1.x <== alpha_m;
    ls1.shift <== diff;
    ls1.skip_checks <== 1;
    signal shifted_alpha_m <== ls1.y;

    signal mm <== shifted_alpha_m + beta_m;
    signal ee <== beta_e;

    signal conditioned_mm;

    component ite = IfThenElse();
    ite.cond <== condition;
    ite.L <== 0;
    ite.R <== mm;
    ite.out ==> conditioned_mm;

    component normalize = Normalize(k, p, 2 * p + 1);
    normalize.e <== ee;
    normalize.m <== conditioned_mm; // conditioned_mm = 0 when condition is true
    normalize.skip_checks <== 1;

    component rac = RoundAndCheck(k, p, 2 * p + 1);
    rac.e <== normalize.e_out;
    rac.m <== normalize.m_out;

    component ite1 = IfThenElse();
    ite1.cond <== condition;
    ite1.L <== alpha_e;
    ite1.R <== rac.e_out;
    ite1.out ==> e_out;

    component ite2 = IfThenElse();
    ite2.cond <== condition;
    ite2.L <== alpha_m;
    ite2.R <== rac.m_out;
    ite2.out ==> m_out;
}
