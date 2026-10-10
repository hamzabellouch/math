import OAI.NumberTheory.Catalan.Energy.BarrierLogRatConstants
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoMaxReduction
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoPointData

namespace OAI

noncomputable section

namespace InternalCatalan

namespace Case2PointData
open InternalCatalan.Case1PointData

theorem X0_normalizations :
    FixedLogNormalization |(X0 : ℝ)| (-1) (2400277287 / 1250000000) ∧
    FixedLogNormalization (1 - (X0 : ℝ)) (0) (4900277287 / 2500000000) ∧
    FixedLogNormalization (1 + (X0 : ℝ) ^ 2) (0) (12011331054488080369 / 6250000000000000000) := by
  norm_num [FixedLogNormalization, X0, Set.mem_Icc]

theorem X1_normalizations :
    FixedLogNormalization |(X1 : ℝ)| (-1) (2235579393 / 1250000000) ∧
    FixedLogNormalization (1 - (X1 : ℝ)) (0) (4735579393 / 2500000000) ∧
    FixedLogNormalization (1 + (X1 : ℝ) ^ 2) (0) (11247815222406248449 / 6250000000000000000) := by
  norm_num [FixedLogNormalization, X1, Set.mem_Icc]

theorem X2_normalizations :
    FixedLogNormalization |(X2 : ℝ)| (-1) (7608305633 / 5000000000) ∧
    FixedLogNormalization (1 - (X2 : ℝ)) (0) (17608305633 / 10000000000) ∧
    FixedLogNormalization (1 + (X2 : ℝ) ^ 2) (0) (157886314605139530689 / 100000000000000000000) := by
  norm_num [FixedLogNormalization, X2, Set.mem_Icc]

theorem X3_normalizations :
    FixedLogNormalization |(X3 : ℝ)| (-1) (3251697397 / 2500000000) ∧
    FixedLogNormalization (1 - (X3 : ℝ)) (0) (8251697397 / 5000000000) ∧
    FixedLogNormalization (1 + (X3 : ℝ) ^ 2) (0) (35573535961656575609 / 25000000000000000000) := by
  norm_num [FixedLogNormalization, X3, Set.mem_Icc]

theorem X4_normalizations :
    FixedLogNormalization |(X4 : ℝ)| (-1) (1037172813 / 1000000000) ∧
    FixedLogNormalization (1 - (X4 : ℝ)) (0) (3037172813 / 2000000000) ∧
    FixedLogNormalization (1 + (X4 : ℝ) ^ 2) (0) (5075727444026332969 / 4000000000000000000) := by
  norm_num [FixedLogNormalization, X4, Set.mem_Icc]

theorem X5_normalizations :
    FixedLogNormalization |(X5 : ℝ)| (-2) (2007817079 / 1250000000) ∧
    FixedLogNormalization (1 - (X5 : ℝ)) (0) (7007817079 / 5000000000) ∧
    FixedLogNormalization (1 + (X5 : ℝ) ^ 2) (0) (29031329422724092241 / 25000000000000000000) := by
  norm_num [FixedLogNormalization, X5, Set.mem_Icc]

theorem X6_normalizations :
    FixedLogNormalization |(X6 : ℝ)| (-2) (1554403323 / 1250000000) ∧
    FixedLogNormalization (1 - (X6 : ℝ)) (0) (6554403323 / 5000000000) ∧
    FixedLogNormalization (1 + (X6 : ℝ) ^ 2) (0) (27416169690553442329 / 25000000000000000000) := by
  norm_num [FixedLogNormalization, X6, Set.mem_Icc]

theorem X7_normalizations :
    FixedLogNormalization |(X7 : ℝ)| (-3) (1033960913 / 625000000) ∧
    FixedLogNormalization (1 - (X7 : ℝ)) (0) (6033960913 / 5000000000) ∧
    FixedLogNormalization (1 + (X7 : ℝ) ^ 2) (0) (26069075169611793569 / 25000000000000000000) := by
  norm_num [FixedLogNormalization, X7, Set.mem_Icc]

theorem X8_normalizations :
    FixedLogNormalization |(X8 : ℝ)| (-3) (198731187 / 156250000) ∧
    FixedLogNormalization (1 - (X8 : ℝ)) (0) (1448731187 / 1250000000) ∧
    FixedLogNormalization (1 + (X8 : ℝ) ^ 2) (0) (1601994084686428969 / 1562500000000000000) := by
  norm_num [FixedLogNormalization, X8, Set.mem_Icc]

theorem X9_normalizations :
    FixedLogNormalization |(X9 : ℝ)| (-3) (765974031 / 625000000) ∧
    FixedLogNormalization (1 - (X9 : ℝ)) (-1) (4234025969 / 2500000000) ∧
    FixedLogNormalization (1 + (X9 : ℝ) ^ 2) (0) (25586716216166388961 / 25000000000000000000) := by
  norm_num [FixedLogNormalization, X9, Set.mem_Icc]

theorem X10_normalizations :
    FixedLogNormalization |(X10 : ℝ)| (-3) (2072448179 / 1250000000) ∧
    FixedLogNormalization (1 - (X10 : ℝ)) (-1) (7927551821 / 5000000000) ∧
    FixedLogNormalization (1 + (X10 : ℝ) ^ 2) (0) (104295041454640416041 / 100000000000000000000) := by
  norm_num [FixedLogNormalization, X10, Set.mem_Icc]

theorem X11_normalizations :
    FixedLogNormalization |(X11 : ℝ)| (-2) (802046621 / 625000000) ∧
    FixedLogNormalization (1 - (X11 : ℝ)) (-1) (1697953379 / 1250000000) ∧
    FixedLogNormalization (1 + (X11 : ℝ) ^ 2) (0) (6893278782257517641 / 6250000000000000000) := by
  norm_num [FixedLogNormalization, X11, Set.mem_Icc]

theorem X12_normalizations :
    FixedLogNormalization |(X12 : ℝ)| (-2) (4381119427 / 2500000000) ∧
    FixedLogNormalization (1 - (X12 : ℝ)) (-1) (5618880573 / 5000000000) ∧
    FixedLogNormalization (1 + (X12 : ℝ) ^ 2) (0) (119194207433636808329 / 100000000000000000000) := by
  norm_num [FixedLogNormalization, X12, Set.mem_Icc]

theorem X13_normalizations :
    FixedLogNormalization |(X13 : ℝ)| (-1) (5851354199 / 5000000000) ∧
    FixedLogNormalization (1 - (X13 : ℝ)) (-2) (4148645801 / 2500000000) ∧
    FixedLogNormalization (1 + (X13 : ℝ) ^ 2) (0) (134238345962154931601 / 100000000000000000000) := by
  norm_num [FixedLogNormalization, X13, Set.mem_Icc]

theorem X14_normalizations :
    FixedLogNormalization |(X14 : ℝ)| (-1) (7269030693 / 5000000000) ∧
    FixedLogNormalization (1 - (X14 : ℝ)) (-2) (2730969307 / 2500000000) ∧
    FixedLogNormalization (1 + (X14 : ℝ) ^ 2) (0) (152838807215776060249 / 100000000000000000000) := by
  norm_num [FixedLogNormalization, X14, Set.mem_Icc]

theorem X15_normalizations :
    FixedLogNormalization |(X15 : ℝ)| (-1) (4195138701 / 2500000000) ∧
    FixedLogNormalization (1 - (X15 : ℝ)) (-3) (804861299 / 625000000) ∧
    FixedLogNormalization (1 + (X15 : ℝ) ^ 2) (0) (42599188720627967401 / 25000000000000000000) := by
  norm_num [FixedLogNormalization, X15, Set.mem_Icc]

theorem X16_normalizations :
    FixedLogNormalization |(X16 : ℝ)| (-1) (2333153641 / 1250000000) ∧
    FixedLogNormalization (1 - (X16 : ℝ)) (-4) (166846359 / 156250000) ∧
    FixedLogNormalization (1 + (X16 : ℝ) ^ 2) (0) (11693605912511556881 / 6250000000000000000) := by
  norm_num [FixedLogNormalization, X16, Set.mem_Icc]

theorem X17_normalizations :
    FixedLogNormalization |(X17 : ℝ)| (-1) (9709786219 / 5000000000) ∧
    FixedLogNormalization (1 - (X17 : ℝ)) (-6) (290213781 / 156250000) ∧
    FixedLogNormalization (1 + (X17 : ℝ) ^ 2) (0) (194279948418682315961 / 100000000000000000000) := by
  norm_num [FixedLogNormalization, X17, Set.mem_Icc]

theorem X18_normalizations :
    FixedLogNormalization |(X18 : ℝ)| (0) (1 / 1) ∧
    FixedLogNormalization (1 - (X18 : ℝ)) (1) (1 / 1) ∧
    FixedLogNormalization (1 + (X18 : ℝ) ^ 2) (1) (1 / 1) := by
  norm_num [FixedLogNormalization, X18, Set.mem_Icc]

theorem Y0_normalizations :
    FixedLogNormalization (Y0 : ℝ) (-6) (88201401 / 78125000) ∧
    FixedLogNormalization (1 - (Y0 : ℝ)) (-1) (4911798599 / 2500000000) := by
  norm_num [FixedLogNormalization, Y0, Set.mem_Icc]

theorem Y1_normalizations :
    FixedLogNormalization (Y1 : ℝ) (-5) (165324703 / 156250000) ∧
    FixedLogNormalization (1 - (Y1 : ℝ)) (-1) (4834675297 / 2500000000) := by
  norm_num [FixedLogNormalization, Y1, Set.mem_Icc]

theorem Y2_normalizations :
    FixedLogNormalization (Y2 : ℝ) (-4) (382476441 / 312500000) ∧
    FixedLogNormalization (1 - (Y2 : ℝ)) (-1) (4617523559 / 2500000000) := by
  norm_num [FixedLogNormalization, Y2, Set.mem_Icc]

theorem Y3_normalizations :
    FixedLogNormalization (Y3 : ℝ) (-4) (1227250753 / 625000000) ∧
    FixedLogNormalization (1 - (Y3 : ℝ)) (-1) (8772749247 / 5000000000) := by
  norm_num [FixedLogNormalization, Y3, Set.mem_Icc]

theorem Y4_normalizations :
    FixedLogNormalization (Y4 : ℝ) (-3) (1074732999 / 625000000) ∧
    FixedLogNormalization (1 - (Y4 : ℝ)) (-1) (3925267001 / 2500000000) := by
  norm_num [FixedLogNormalization, Y4, Set.mem_Icc]

theorem Y5_normalizations :
    FixedLogNormalization (Y5 : ℝ) (-2) (381023639 / 312500000) ∧
    FixedLogNormalization (1 - (Y5 : ℝ)) (-1) (868976361 / 625000000) := by
  norm_num [FixedLogNormalization, Y5, Set.mem_Icc]

theorem Y6_normalizations :
    FixedLogNormalization (Y6 : ℝ) (-2) (540337387 / 312500000) ∧
    FixedLogNormalization (1 - (Y6 : ℝ)) (-1) (709662613 / 625000000) := by
  norm_num [FixedLogNormalization, Y6, Set.mem_Icc]

theorem Y7_normalizations :
    FixedLogNormalization (Y7 : ℝ) (-1) (2782378997 / 2500000000) ∧
    FixedLogNormalization (1 - (Y7 : ℝ)) (-2) (2217621003 / 1250000000) := by
  norm_num [FixedLogNormalization, Y7, Set.mem_Icc]

theorem Y8_normalizations :
    FixedLogNormalization (Y8 : ℝ) (-1) (6801929373 / 5000000000) ∧
    FixedLogNormalization (1 - (Y8 : ℝ)) (-2) (3198070627 / 2500000000) := by
  norm_num [FixedLogNormalization, Y8, Set.mem_Icc]

theorem Y9_normalizations :
    FixedLogNormalization (Y9 : ℝ) (-1) (8031988371 / 5000000000) ∧
    FixedLogNormalization (1 - (Y9 : ℝ)) (-3) (1968011629 / 1250000000) := by
  norm_num [FixedLogNormalization, Y9, Set.mem_Icc]

theorem Y10_normalizations :
    FixedLogNormalization (Y10 : ℝ) (-1) (8877037851 / 5000000000) ∧
    FixedLogNormalization (1 - (Y10 : ℝ)) (-4) (1122962149 / 625000000) := by
  norm_num [FixedLogNormalization, Y10, Set.mem_Icc]

theorem Y11_normalizations :
    FixedLogNormalization (Y11 : ℝ) (-1) (1197220229 / 625000000) ∧
    FixedLogNormalization (1 - (Y11 : ℝ)) (-5) (52779771 / 39062500) := by
  norm_num [FixedLogNormalization, Y11, Set.mem_Icc]

theorem Y12_normalizations :
    FixedLogNormalization (Y12 : ℝ) (-1) (9838463999 / 5000000000) ∧
    FixedLogNormalization (1 - (Y12 : ℝ)) (-6) (161536001 / 156250000) := by
  norm_num [FixedLogNormalization, Y12, Set.mem_Icc]

theorem Y13_normalizations :
    FixedLogNormalization (Y13 : ℝ) (-1) (1994545563 / 1000000000) ∧
    FixedLogNormalization (1 - (Y13 : ℝ)) (-9) (5454437 / 3906250) := by
  norm_num [FixedLogNormalization, Y13, Set.mem_Icc]

theorem Y14_normalizations :
    FixedLogNormalization (Y14 : ℝ) (-1) (2498009299 / 1250000000) ∧
    FixedLogNormalization (1 - (Y14 : ℝ)) (-11) (15925608 / 9765625) := by
  norm_num [FixedLogNormalization, Y14, Set.mem_Icc]

theorem Y15_normalizations :
    FixedLogNormalization (Y15 : ℝ) (-2) (1 / 1) ∧
    FixedLogNormalization (1 - (Y15 : ℝ)) (-1) (3 / 2) := by
  norm_num [FixedLogNormalization, Y15, Set.mem_Icc]

theorem Y16_normalizations :
    FixedLogNormalization (Y16 : ℝ) (-1) (1 / 1) ∧
    FixedLogNormalization (1 - (Y16 : ℝ)) (-1) (1 / 1) := by
  norm_num [FixedLogNormalization, Y16, Set.mem_Icc]

theorem Y17_normalizations :
    FixedLogNormalization (Y17 : ℝ) (-1) (3 / 2) ∧
    FixedLogNormalization (1 - (Y17 : ℝ)) (-2) (1 / 1) := by
  norm_num [FixedLogNormalization, Y17, Set.mem_Icc]

end Case2PointData

def barrierCase2XApproxRat (x : ℚ) (m0 m1 m2 : ℤ) (y0 y1 y2 : ℚ) : ℚ :=
  (19 / 48 : ℚ) * barrierScaledLogRat m0 y0 +
    (1 / 12 : ℚ) * barrierScaledLogRat m1 y1 -
    (65 / 48 : ℚ) * barrierScaledLogRat m2 y2 + barrierCase2XRat x

def barrierCase2YApproxRat (x : ℚ) (m0 m1 : ℤ) (y0 y1 : ℚ) : ℚ :=
  (7 / 48 : ℚ) * barrierScaledLogRat m0 y0 +
    (1 / 12 : ℚ) * barrierScaledLogRat m1 y1 + barrierCase2YRat x

theorem barrierCase2X_realLog_approx_error (x : ℚ) (hx : |(x : ℝ)| ≤ 1)
    (m0 m1 m2 : ℤ) (y0 y1 y2 : ℚ)
    (h0 : Case1PointData.FixedLogNormalization |(x : ℝ)| m0 y0)
    (h1 : Case1PointData.FixedLogNormalization (1 - (x : ℝ)) m1 y1)
    (h2 : Case1PointData.FixedLogNormalization (1 + (x : ℝ) ^ 2) m2 y2) :
    |barrierCase2X (x : ℝ) -
      (((barrierCase2XApproxRat x m0 m1 m2 y0 y1 y2 : ℚ) : ℝ) +
        (barrierP2Tail.map (barrierCase2XPLogTerm (x : ℝ))).sum +
        (barrierV2Tail.map (barrierCase2XVLogTerm (x : ℝ))).sum)| <
      (2 / 1000000000000000 : ℝ) := by
  have he0 := abs_lt.mp (barrier_fixed_log_abs_error h0)
  have he1 := abs_lt.mp (barrier_fixed_log_abs_error h1)
  have he2 := abs_lt.mp (barrier_fixed_log_abs_error h2)
  rw [barrierCase2X_eval_rat x hx]
  unfold barrierCase2XApproxRat
  push_cast
  apply abs_lt.mpr
  constructor <;> linarith [he0.1, he0.2, he1.1, he1.2, he2.1, he2.2]

theorem barrierCase2Y_realLog_approx_error (x : ℚ) (hx : |(x : ℝ)| ≤ 1)
    (m0 m1 : ℤ) (y0 y1 : ℚ)
    (h0 : Case1PointData.FixedLogNormalization (x : ℝ) m0 y0)
    (h1 : Case1PointData.FixedLogNormalization (1 - (x : ℝ)) m1 y1) :
    |barrierCase2Y (x : ℝ) -
      (((barrierCase2YApproxRat x m0 m1 y0 y1 : ℚ) : ℝ) +
        (barrierV2Tail.map (barrierCase2YVLogTerm (x : ℝ))).sum)| <
      (1 / 1000000000000000 : ℝ) := by
  have he0 := abs_lt.mp (barrier_fixed_log_abs_error h0)
  have he1 := abs_lt.mp (barrier_fixed_log_abs_error h1)
  rw [barrierCase2Y_eval_rat x hx]
  unfold barrierCase2YApproxRat
  push_cast
  apply abs_lt.mpr
  constructor <;> linarith [he0.1, he0.2, he1.1, he1.2]

end InternalCatalan

end

end OAI
