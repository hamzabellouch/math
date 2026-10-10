import OAI.NumberTheory.Catalan.Estimates.ManuscriptCaseTwoYAllPrecision

namespace OAI

section

noncomputable section

namespace InternalCatalan

def manuscriptCase2Y8RoundedSubstituteRat : ℚ :=
  manuscriptRoundedYFieldRat (barrierCase2YRat Case2PointData.Y8) (-1) (-2) (6801929373 / 5000000000) (3198070627 / 2500000000) +
    (manuscriptRoundedWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (2) (0) (290768295341780173129 / 156250000000000000000) (0 / 1)) +
    (manuscriptRoundedWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (3) (0) (2543264390303471558161 / 1953125000000000000000) (0 / 1)) +
    (manuscriptRoundedWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (-2) (0) (1301678142383500948609 / 976562500000000000000) (0 / 1)) +
    (manuscriptRoundedWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (-2) (0) (3722627891392642499569 / 2500000000000000000000) (0 / 1)) +
    (manuscriptRoundedWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (-2) (0) (154860105278932459268641 / 97656250000000000000000) (0 / 1)) +
    (manuscriptRoundedWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (0) (-2) (79955365900021143329209 / 62500000000000000000000) (97900000000 / 265275245547)) +
    (manuscriptRoundedWeightedComplexLogRat (-13619357 / 100000000) (-(-600749 / 3125000)) (0) (-(-2)) (79955365900021143329209 / 62500000000000000000000) (-(97900000000 / 265275245547))) +
    (manuscriptRoundedWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (0) (-2) (3837815698817694023449 / 2500000000000000000000) (9500000000 / 61217364357)) +
    (manuscriptRoundedWeightedComplexLogRat (7835271 / 50000000) (-(-15094393 / 100000000)) (0) (-(-2)) (3837815698817694023449 / 2500000000000000000000) (-(9500000000 / 61217364357))) +
    (manuscriptRoundedWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (0) (-2) (1695578418632015995919049 / 1000000000000000000000000) (29325000000 / 433056170081)) +
    (manuscriptRoundedWeightedComplexLogRat (3346771 / 100000000) (-(5956127 / 100000000)) (0) (-(-2)) (1695578418632015995919049 / 1000000000000000000000000) (-(29325000000 / 433056170081))) +
    (manuscriptRoundedWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (0) (-2) (700355618901393739268641 / 390625000000000000000000) (19840000000 / 836637312879)) +
    (manuscriptRoundedWeightedComplexLogRat (-2055213 / 200000000) (-(-21715849 / 200000000)) (0) (-(-2)) (700355618901393739268641 / 390625000000000000000000) (-(19840000000 / 836637312879)))

theorem manuscript_case2Y8_additional_rounding_error :
    |(manuscriptCase2Y8SubstituteRat : ℝ) - (manuscriptCase2Y8RoundedSubstituteRat : ℝ)| < (1 / 10 ^ 32 : ℝ) := by
  let a0 : ℚ := barrierCase2YApproxRat Case2PointData.Y8 (-1) (-2) (6801929373 / 5000000000) (3198070627 / 2500000000)
  let r0 : ℚ := manuscriptRoundedYFieldRat (barrierCase2YRat Case2PointData.Y8) (-1) (-2) (6801929373 / 5000000000) (3198070627 / 2500000000)
  let e0 : ℝ := ((7 / 48 : ℝ) + 1 / 12) * (3636 * manuscriptTermRoundStep)
  let a1 : ℚ := (barrierWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (2) (0) (290768295341780173129 / 156250000000000000000) (0 / 1))
  let r1 : ℚ := (manuscriptRoundedWeightedComplexLogRat (-15199211 / 100000000) (0 / 1) (2) (0) (290768295341780173129 / 156250000000000000000) (0 / 1))
  let e1 : ℝ := (|(((-15199211 / 100000000) : ℚ) : ℝ)| + |(((0 / 1) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  let a2 : ℚ := (barrierWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (3) (0) (2543264390303471558161 / 1953125000000000000000) (0 / 1))
  let r2 : ℚ := (manuscriptRoundedWeightedComplexLogRat (-2225831 / 50000000) (0 / 1) (3) (0) (2543264390303471558161 / 1953125000000000000000) (0 / 1))
  let e2 : ℝ := (|(((-2225831 / 50000000) : ℚ) : ℝ)| + |(((0 / 1) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  let a3 : ℚ := (barrierWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (-2) (0) (1301678142383500948609 / 976562500000000000000) (0 / 1))
  let r3 : ℚ := (manuscriptRoundedWeightedComplexLogRat (-1272699 / 50000000) (0 / 1) (-2) (0) (1301678142383500948609 / 976562500000000000000) (0 / 1))
  let e3 : ℝ := (|(((-1272699 / 50000000) : ℚ) : ℝ)| + |(((0 / 1) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  let a4 : ℚ := (barrierWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (-2) (0) (3722627891392642499569 / 2500000000000000000000) (0 / 1))
  let r4 : ℚ := (manuscriptRoundedWeightedComplexLogRat (2466317 / 50000000) (0 / 1) (-2) (0) (3722627891392642499569 / 2500000000000000000000) (0 / 1))
  let e4 : ℝ := (|(((2466317 / 50000000) : ℚ) : ℝ)| + |(((0 / 1) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  let a5 : ℚ := (barrierWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (-2) (0) (154860105278932459268641 / 97656250000000000000000) (0 / 1))
  let r5 : ℚ := (manuscriptRoundedWeightedComplexLogRat (-11618157 / 100000000) (0 / 1) (-2) (0) (154860105278932459268641 / 97656250000000000000000) (0 / 1))
  let e5 : ℝ := (|(((-11618157 / 100000000) : ℚ) : ℝ)| + |(((0 / 1) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  let a6 : ℚ := (barrierWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (0) (-2) (79955365900021143329209 / 62500000000000000000000) (97900000000 / 265275245547))
  let r6 : ℚ := (manuscriptRoundedWeightedComplexLogRat (-13619357 / 100000000) (-600749 / 3125000) (0) (-2) (79955365900021143329209 / 62500000000000000000000) (97900000000 / 265275245547))
  let e6 : ℝ := (|(((-13619357 / 100000000) : ℚ) : ℝ)| + |(((-600749 / 3125000) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  let a7 : ℚ := (barrierWeightedComplexLogRat (-13619357 / 100000000) (-(-600749 / 3125000)) (0) (-(-2)) (79955365900021143329209 / 62500000000000000000000) (-(97900000000 / 265275245547)))
  let r7 : ℚ := (manuscriptRoundedWeightedComplexLogRat (-13619357 / 100000000) (-(-600749 / 3125000)) (0) (-(-2)) (79955365900021143329209 / 62500000000000000000000) (-(97900000000 / 265275245547)))
  let e7 : ℝ := (|(((-13619357 / 100000000) : ℚ) : ℝ)| + |(((-(-600749 / 3125000)) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  let a8 : ℚ := (barrierWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (0) (-2) (3837815698817694023449 / 2500000000000000000000) (9500000000 / 61217364357))
  let r8 : ℚ := (manuscriptRoundedWeightedComplexLogRat (7835271 / 50000000) (-15094393 / 100000000) (0) (-2) (3837815698817694023449 / 2500000000000000000000) (9500000000 / 61217364357))
  let e8 : ℝ := (|(((7835271 / 50000000) : ℚ) : ℝ)| + |(((-15094393 / 100000000) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  let a9 : ℚ := (barrierWeightedComplexLogRat (7835271 / 50000000) (-(-15094393 / 100000000)) (0) (-(-2)) (3837815698817694023449 / 2500000000000000000000) (-(9500000000 / 61217364357)))
  let r9 : ℚ := (manuscriptRoundedWeightedComplexLogRat (7835271 / 50000000) (-(-15094393 / 100000000)) (0) (-(-2)) (3837815698817694023449 / 2500000000000000000000) (-(9500000000 / 61217364357)))
  let e9 : ℝ := (|(((7835271 / 50000000) : ℚ) : ℝ)| + |(((-(-15094393 / 100000000)) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  let a10 : ℚ := (barrierWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (0) (-2) (1695578418632015995919049 / 1000000000000000000000000) (29325000000 / 433056170081))
  let r10 : ℚ := (manuscriptRoundedWeightedComplexLogRat (3346771 / 100000000) (5956127 / 100000000) (0) (-2) (1695578418632015995919049 / 1000000000000000000000000) (29325000000 / 433056170081))
  let e10 : ℝ := (|(((3346771 / 100000000) : ℚ) : ℝ)| + |(((5956127 / 100000000) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  let a11 : ℚ := (barrierWeightedComplexLogRat (3346771 / 100000000) (-(5956127 / 100000000)) (0) (-(-2)) (1695578418632015995919049 / 1000000000000000000000000) (-(29325000000 / 433056170081)))
  let r11 : ℚ := (manuscriptRoundedWeightedComplexLogRat (3346771 / 100000000) (-(5956127 / 100000000)) (0) (-(-2)) (1695578418632015995919049 / 1000000000000000000000000) (-(29325000000 / 433056170081)))
  let e11 : ℝ := (|(((3346771 / 100000000) : ℚ) : ℝ)| + |(((-(5956127 / 100000000)) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  let a12 : ℚ := (barrierWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (0) (-2) (700355618901393739268641 / 390625000000000000000000) (19840000000 / 836637312879))
  let r12 : ℚ := (manuscriptRoundedWeightedComplexLogRat (-2055213 / 200000000) (-21715849 / 200000000) (0) (-2) (700355618901393739268641 / 390625000000000000000000) (19840000000 / 836637312879))
  let e12 : ℝ := (|(((-2055213 / 200000000) : ℚ) : ℝ)| + |(((-21715849 / 200000000) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  let a13 : ℚ := (barrierWeightedComplexLogRat (-2055213 / 200000000) (-(-21715849 / 200000000)) (0) (-(-2)) (700355618901393739268641 / 390625000000000000000000) (-(19840000000 / 836637312879)))
  let r13 : ℚ := (manuscriptRoundedWeightedComplexLogRat (-2055213 / 200000000) (-(-21715849 / 200000000)) (0) (-(-2)) (700355618901393739268641 / 390625000000000000000000) (-(19840000000 / 836637312879)))
  let e13 : ℝ := (|(((-2055213 / 200000000) : ℚ) : ℝ)| + |(((-(-21715849 / 200000000)) : ℚ) : ℝ)|) * (3636 * manuscriptTermRoundStep)
  have h0 : |(a0 : ℝ) - (r0 : ℝ)| ≤ e0 := by
    exact manuscript_rounded_y_field_error_le (barrierCase2YRat Case2PointData.Y8) (-1) (-2) (6801929373 / 5000000000) (3198070627 / 2500000000) (by norm_num) (by norm_num)
  have h1 : |(a1 : ℝ) - (r1 : ℝ)| ≤ e1 := by
    exact manuscript_rounded_weighted_complex_log_error_le (-15199211 / 100000000) (0 / 1) (2) (0) (290768295341780173129 / 156250000000000000000) (0 / 1) (by norm_num) (by norm_num)
  have h2 : |(a2 : ℝ) - (r2 : ℝ)| ≤ e2 := by
    exact manuscript_rounded_weighted_complex_log_error_le (-2225831 / 50000000) (0 / 1) (3) (0) (2543264390303471558161 / 1953125000000000000000) (0 / 1) (by norm_num) (by norm_num)
  have h3 : |(a3 : ℝ) - (r3 : ℝ)| ≤ e3 := by
    exact manuscript_rounded_weighted_complex_log_error_le (-1272699 / 50000000) (0 / 1) (-2) (0) (1301678142383500948609 / 976562500000000000000) (0 / 1) (by norm_num) (by norm_num)
  have h4 : |(a4 : ℝ) - (r4 : ℝ)| ≤ e4 := by
    exact manuscript_rounded_weighted_complex_log_error_le (2466317 / 50000000) (0 / 1) (-2) (0) (3722627891392642499569 / 2500000000000000000000) (0 / 1) (by norm_num) (by norm_num)
  have h5 : |(a5 : ℝ) - (r5 : ℝ)| ≤ e5 := by
    exact manuscript_rounded_weighted_complex_log_error_le (-11618157 / 100000000) (0 / 1) (-2) (0) (154860105278932459268641 / 97656250000000000000000) (0 / 1) (by norm_num) (by norm_num)
  have h6 : |(a6 : ℝ) - (r6 : ℝ)| ≤ e6 := by
    exact manuscript_rounded_weighted_complex_log_error_le (-13619357 / 100000000) (-600749 / 3125000) (0) (-2) (79955365900021143329209 / 62500000000000000000000) (97900000000 / 265275245547) (by norm_num) (by norm_num)
  have h7 : |(a7 : ℝ) - (r7 : ℝ)| ≤ e7 := by
    exact manuscript_rounded_weighted_complex_log_error_le (-13619357 / 100000000) (-(-600749 / 3125000)) (0) (-(-2)) (79955365900021143329209 / 62500000000000000000000) (-(97900000000 / 265275245547)) (by norm_num) (by norm_num)
  have h8 : |(a8 : ℝ) - (r8 : ℝ)| ≤ e8 := by
    exact manuscript_rounded_weighted_complex_log_error_le (7835271 / 50000000) (-15094393 / 100000000) (0) (-2) (3837815698817694023449 / 2500000000000000000000) (9500000000 / 61217364357) (by norm_num) (by norm_num)
  have h9 : |(a9 : ℝ) - (r9 : ℝ)| ≤ e9 := by
    exact manuscript_rounded_weighted_complex_log_error_le (7835271 / 50000000) (-(-15094393 / 100000000)) (0) (-(-2)) (3837815698817694023449 / 2500000000000000000000) (-(9500000000 / 61217364357)) (by norm_num) (by norm_num)
  have h10 : |(a10 : ℝ) - (r10 : ℝ)| ≤ e10 := by
    exact manuscript_rounded_weighted_complex_log_error_le (3346771 / 100000000) (5956127 / 100000000) (0) (-2) (1695578418632015995919049 / 1000000000000000000000000) (29325000000 / 433056170081) (by norm_num) (by norm_num)
  have h11 : |(a11 : ℝ) - (r11 : ℝ)| ≤ e11 := by
    exact manuscript_rounded_weighted_complex_log_error_le (3346771 / 100000000) (-(5956127 / 100000000)) (0) (-(-2)) (1695578418632015995919049 / 1000000000000000000000000) (-(29325000000 / 433056170081)) (by norm_num) (by norm_num)
  have h12 : |(a12 : ℝ) - (r12 : ℝ)| ≤ e12 := by
    exact manuscript_rounded_weighted_complex_log_error_le (-2055213 / 200000000) (-21715849 / 200000000) (0) (-2) (700355618901393739268641 / 390625000000000000000000) (19840000000 / 836637312879) (by norm_num) (by norm_num)
  have h13 : |(a13 : ℝ) - (r13 : ℝ)| ≤ e13 := by
    exact manuscript_rounded_weighted_complex_log_error_le (-2055213 / 200000000) (-(-21715849 / 200000000)) (0) (-(-2)) (700355618901393739268641 / 390625000000000000000000) (-(19840000000 / 836637312879)) (by norm_num) (by norm_num)
  have hs1 := manuscript_rat_add_rounding_error (a0) (r0) a1 r1 h0 h1
  have hs2 := manuscript_rat_add_rounding_error (a0 + a1) (r0 + r1) a2 r2 hs1 h2
  have hs3 := manuscript_rat_add_rounding_error (a0 + a1 + a2) (r0 + r1 + r2) a3 r3 hs2 h3
  have hs4 := manuscript_rat_add_rounding_error (a0 + a1 + a2 + a3) (r0 + r1 + r2 + r3) a4 r4 hs3 h4
  have hs5 := manuscript_rat_add_rounding_error (a0 + a1 + a2 + a3 + a4) (r0 + r1 + r2 + r3 + r4) a5 r5 hs4 h5
  have hs6 := manuscript_rat_add_rounding_error (a0 + a1 + a2 + a3 + a4 + a5) (r0 + r1 + r2 + r3 + r4 + r5) a6 r6 hs5 h6
  have hs7 := manuscript_rat_add_rounding_error (a0 + a1 + a2 + a3 + a4 + a5 + a6) (r0 + r1 + r2 + r3 + r4 + r5 + r6) a7 r7 hs6 h7
  have hs8 := manuscript_rat_add_rounding_error (a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7) (r0 + r1 + r2 + r3 + r4 + r5 + r6 + r7) a8 r8 hs7 h8
  have hs9 := manuscript_rat_add_rounding_error (a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8) (r0 + r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8) a9 r9 hs8 h9
  have hs10 := manuscript_rat_add_rounding_error (a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9) (r0 + r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9) a10 r10 hs9 h10
  have hs11 := manuscript_rat_add_rounding_error (a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9 + a10) (r0 + r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9 + r10) a11 r11 hs10 h11
  have hs12 := manuscript_rat_add_rounding_error (a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9 + a10 + a11) (r0 + r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9 + r10 + r11) a12 r12 hs11 h12
  have hs13 := manuscript_rat_add_rounding_error (a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9 + a10 + a11 + a12) (r0 + r1 + r2 + r3 + r4 + r5 + r6 + r7 + r8 + r9 + r10 + r11 + r12) a13 r13 hs12 h13
  have hbudget : e0 + e1 + e2 + e3 + e4 + e5 + e6 + e7 + e8 + e9 + e10 + e11 + e12 + e13 < (1 / 10 ^ 32 : ℝ) := by
    norm_num [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, manuscriptTermRoundStep]
  change |(manuscriptCase2Y8SubstituteRat : ℝ) - (manuscriptCase2Y8RoundedSubstituteRat : ℝ)| ≤ e0 + e1 + e2 + e3 + e4 + e5 + e6 + e7 + e8 + e9 + e10 + e11 + e12 + e13 at hs13
  exact hs13.trans_lt hbudget

end InternalCatalan

end

end

end OAI
