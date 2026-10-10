import OAI.Analysis.Pureness.Quasitrace.QuasitraceMetricSize

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace
open scoped NNReal
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
variable (T : PositiveQuasitrace D)
variable (hsqrt : ∀ a b : Positive D, Real.sqrt (T (Positive.add a b)) ≤ Real.sqrt (T a)+Real.sqrt (T b))

include hsqrt in

theorem square_add_weighted_of_sqrt_add (x y : D) (r : ℝ) (hr : r ≠ 0) :
    T (Positive.starMul (x+y)) ≤
      (Real.sqrt ((1+r*r)*T (Positive.starMul x))+
        Real.sqrt ((1+r⁻¹*r⁻¹)*T (Positive.starMul y)))^2 := by
  let u : ℝ≥0 := ⟨1+r*r,by nlinarith [sq_nonneg r]⟩
  let v : ℝ≥0 := ⟨1+r⁻¹*r⁻¹,by nlinarith [sq_nonneg r⁻¹]⟩
  have ho : Positive.starMul (x+y) ≤ Positive.add
      (Positive.smul u (Positive.starMul x)) (Positive.smul v (Positive.starMul y)) :=
    star_square_add_le_weighted x y r hr
  have hs := hsqrt (Positive.smul u (Positive.starMul x)) (Positive.smul v (Positive.starMul y))
  rw [T.map_smul,T.map_smul] at hs
  exact (T.monotone ho).trans (by
    have hsq := (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mpr hs
    rwa [Real.sq_sqrt (T.nonneg _)] at hsq)

include hsqrt in

theorem metricSize_add_of_sqrt_add (x y : D) :
    T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y := by
  have hc := weighted_scalar_cube_bound (T (Positive.starMul x)) (T (Positive.starMul y))
    (T (Positive.starMul (x+y))) (T.nonneg _) (T.nonneg _)
    (fun r hr => T.square_add_weighted_of_sqrt_add hsqrt x y r hr)
  have h : T.metricSize (x+y)^3 ≤ (T.metricSize x+T.metricSize y)^3 := by
    rw [T.metricSize_cube]
    exact hc
  exact (pow_le_pow_iff_left₀ (T.metricSize_nonneg _)
    (add_nonneg (T.metricSize_nonneg _) (T.metricSize_nonneg _)) (by decide : 3 ≠ 0)).mp h
end CuntzPureness.PositiveQuasitrace

end

end OAI
