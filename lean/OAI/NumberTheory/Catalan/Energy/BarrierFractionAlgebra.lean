import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoXExplicitGroup7

namespace OAI

namespace InternalCatalan

open Polynomial

theorem barrierFractionProduct_append_exact (fs gs : List (ℚ[X] × ℚ[X])) :
    barrierFractionProduct (fs ++ gs) =
      barrierFractionProduct fs * barrierFractionProduct gs := by
  simp only [barrierFractionProduct, List.map_append, List.prod_append]

theorem barrierFractionNumerator_append_exact (fs gs : List (ℚ[X] × ℚ[X])) :
    barrierFractionNumerator (fs ++ gs) =
      barrierFractionNumerator fs * barrierFractionProduct gs +
        barrierFractionProduct fs * barrierFractionNumerator gs := by
  induction fs with
  | nil =>
      simp only [List.nil_append, barrierFractionNumerator, barrierFractionProduct,
        List.map_nil, List.prod_nil, zero_mul, one_mul, zero_add]
  | cons aq fs ih =>
      change aq.1 * barrierFractionProduct (fs ++ gs) +
          aq.2 * barrierFractionNumerator (fs ++ gs) =
        (aq.1 * barrierFractionProduct fs + aq.2 * barrierFractionNumerator fs) *
            barrierFractionProduct gs +
          (aq.2 * barrierFractionProduct fs) * barrierFractionNumerator gs
      rw [barrierFractionProduct_append_exact, ih]
      ring

theorem barrierFractionProduct_scale_exact (c : ℚ) (fs : List (ℚ[X] × ℚ[X])) :
    barrierFractionProduct (barrierScaleFractions c fs) = barrierFractionProduct fs := by
  simp only [barrierFractionProduct, barrierScaleFractions, List.map_map,
    Function.comp_def]

theorem barrierFractionNumerator_scale_exact (c : ℚ) (fs : List (ℚ[X] × ℚ[X])) :
    barrierFractionNumerator (barrierScaleFractions c fs) =
      C c * barrierFractionNumerator fs := by
  induction fs with
  | nil =>
      simp only [barrierScaleFractions, List.map_nil, barrierFractionNumerator, mul_zero]
  | cons aq fs ih =>
      change (C c * aq.1) * barrierFractionProduct (barrierScaleFractions c fs) +
          aq.2 * barrierFractionNumerator (barrierScaleFractions c fs) =
        C c * (aq.1 * barrierFractionProduct fs + aq.2 * barrierFractionNumerator fs)
      rw [barrierFractionProduct_scale_exact, ih]
      ring

end InternalCatalan

end OAI
