import OAI.Analysis.Pureness.Operators.WeightedStarSquare
import OAI.Analysis.Pureness.Operators.WeightedCubeOptimization

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace
open scoped NNReal ENNReal
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

def PositiveQuasitrace.metricSize (T : PositiveQuasitrace D) (x : D) : ℝ :=
  (T (Positive.starMul x))^((3:ℝ)⁻¹)

namespace PositiveQuasitrace
variable (T : PositiveQuasitrace D)
lemma metricSize_nonneg (x : D) : 0 ≤ T.metricSize x := Real.rpow_nonneg (T.nonneg _) _
lemma metricSize_cube (x : D) : T.metricSize x ^ 3 = T (Positive.starMul x) :=
  Real.rpow_inv_natCast_pow (T.nonneg _) (by norm_num)
lemma metricSize_eq_twoSize (x : D) : T.metricSize x = T.twoSize x ^ (2/3:ℝ) := by
  unfold metricSize twoSize
  rw [Real.sqrt_eq_rpow,← Real.rpow_mul (T.nonneg _)]
  norm_num
lemma metricSize_zero : T.metricSize 0 = 0 := by
  have hz : Positive.starMul (0 : D) = Positive.zero := Subtype.ext (by simp [Positive.starMul,Positive.zero])
  simp [metricSize,hz,T.map_zero]
lemma metricSize_neg (x : D) : T.metricSize (-x) = T.metricSize x := by
  have hz : Positive.starMul (-x) = Positive.starMul x := Subtype.ext (by simp [Positive.starMul])
  simp only [metricSize,hz]
lemma metricSize_star (x : D) : T.metricSize (star x) = T.metricSize x := by
  rw [T.metricSize_eq_twoSize,T.metricSize_eq_twoSize,T.twoSize_star]
lemma metricSize_mul_le_left (x y : D) :
    T.metricSize (x*y) ≤ ‖x‖^(2/3:ℝ)*T.metricSize y := by
  have h := Real.rpow_le_rpow (T.twoSize_nonneg (x*y)) (T.twoSize_mul_le_left x y)
    (show 0 ≤ (2/3:ℝ) by norm_num)
  rw [Real.mul_rpow (norm_nonneg _) (T.twoSize_nonneg _)] at h
  simpa only [T.metricSize_eq_twoSize] using h
lemma metricSize_mul_le_right (x y : D) :
    T.metricSize (x*y) ≤ T.metricSize x*‖y‖^(2/3:ℝ) := by
  have h := T.metricSize_mul_le_left (star y) (star x)
  rw [← star_mul,T.metricSize_star,T.metricSize_star,norm_star] at h
  simpa only [mul_comm] using h
lemma metricSize_eq_zero_iff (hfaith : ∀ a : Positive D, a.1 ≠ 0 → 0 < T a) (x : D) :
    T.metricSize x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have ht : T (Positive.starMul x) = 0 := by rw [← T.metricSize_cube x,h]; norm_num
    by_contra hx
    have hs : (Positive.starMul x).1 ≠ 0 := by
      change star x*x ≠ 0
      intro hz
      have hn := CStarRing.norm_star_mul_self (x := x)
      rw [hz,norm_zero] at hn
      exact hx (norm_eq_zero.mp (by nlinarith [norm_nonneg x]))
    exact (hfaith _ hs).ne' ht
  · rintro rfl; exact T.metricSize_zero
end PositiveQuasitrace

theorem finiteSpectralPositiveQuasitrace_metricSize_add
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
    (hlsc : ∀ n, LowerSemicontinuous (fun M : Positive (FinMatrix A n) => d (finitePositiveClass n M)))
    (hfinite : ∀ x, d x ≠ ⊤) (n : ℕ) (x y : FinMatrix A n) :
    let T := finiteSpectralPositiveQuasitrace d hd hlsc hfinite n
    T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y := by
  let T := finiteSpectralPositiveQuasitrace d hd hlsc hfinite n
  have hc := weighted_scalar_cube_bound (T (Positive.starMul x)) (T (Positive.starMul y))
    (T (Positive.starMul (x+y))) (T.nonneg _) (T.nonneg _)
    (fun r hr => finiteSpectralPositiveQuasitrace_square_add_weighted d hd hlsc hfinite n x y r hr)
  have h : T.metricSize (x+y)^3 ≤ (T.metricSize x+T.metricSize y)^3 := by
    rw [T.metricSize_cube]
    exact hc
  exact (pow_le_pow_iff_left₀ (T.metricSize_nonneg _)
    (add_nonneg (T.metricSize_nonneg _) (T.metricSize_nonneg _)) (by decide : 3 ≠ 0)).mp h
end CuntzPureness

end

end OAI
