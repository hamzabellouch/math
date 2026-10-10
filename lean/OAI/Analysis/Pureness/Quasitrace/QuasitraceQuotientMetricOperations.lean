import OAI.Analysis.Pureness.Quasitrace.QuasitraceQuotientHomogeneity

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace Filter
open scoped Topology NNReal ENNReal ComplexOrder
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]
variable (T : CuntzPureness.PositiveQuasitrace D)
variable (hadd : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)
variable (hsqrt : ∀ a b : Positive D, Real.sqrt (T (Positive.add a b)) ≤ Real.sqrt (T a)+Real.sqrt (T b))

lemma quotientSquareValue_mul_le_left (x y : T.CauchyQuotient hadd) :
    (T.quotientValue hadd hsqrt (star (x*y)*(x*y))).re ≤
      ‖x‖^2*(T.quotientValue hadd hsqrt (star y*y)).re := by
  have h : Positive.starMul (x*y) ≤ Positive.smul (‖x‖₊^2) (Positive.starMul y) := by
    change star (x*y)*(x*y) ≤ (‖x‖₊^2 : ℝ≥0) • (star y*y)
    simp only [NNReal.smul_def,NNReal.coe_pow,coe_nnnorm,star_mul]
    rw [← mul_assoc,mul_assoc (star y) (star x),sq,← CStarRing.norm_star_mul_self (x := x)]
    exact CStarAlgebra.star_left_conjugate_le_norm_smul y (star x * x)
  have hv := T.quotientValue_positive_mono hadd hsqrt h
  have hvr := (Complex.le_def.mp hv).1
  change (T.quotientValue hadd hsqrt (star (x*y)*(x*y))).re ≤
    (T.quotientValue hadd hsqrt ((‖x‖^2 : ℝ) • (star y*y))).re at hvr
  rwa [T.quotientValue_real_smul_re] at hvr

lemma quotientMetricSize_mul_le_left (x y : T.CauchyQuotient hadd) :
    T.quotientMetricSize hadd hsqrt (x*y) ≤ ‖x‖^(2/3:ℝ)*T.quotientMetricSize hadd hsqrt y := by
  have hx := (Complex.nonneg_iff.mp (T.quotientValue_square_nonneg hadd hsqrt (x*y))).1
  have hy := (Complex.nonneg_iff.mp (T.quotientValue_square_nonneg hadd hsqrt y)).1
  have h := Real.rpow_le_rpow hx (T.quotientSquareValue_mul_le_left hadd hsqrt x y)
    (show 0 ≤ (3:ℝ)⁻¹ by positivity)
  rw [Real.mul_rpow (sq_nonneg _) hy] at h
  have he : (‖x‖^2)^((3:ℝ)⁻¹) = ‖x‖^(2/3:ℝ) := by
    rw [← Real.rpow_two,← Real.rpow_mul (norm_nonneg _)]
    congr 1
  rw [he] at h
  exact h

lemma quotientMetricSize_mul_le_right (x y : T.CauchyQuotient hadd) :
    T.quotientMetricSize hadd hsqrt (x*y) ≤ T.quotientMetricSize hadd hsqrt x*‖y‖^(2/3:ℝ) := by
  have h := T.quotientMetricSize_mul_le_left hadd hsqrt (star y) (star x)
  rw [← star_mul,T.quotientMetricSize_star,T.quotientMetricSize_star,norm_star] at h
  rw [mul_comm (‖y‖^(2/3:ℝ)) (T.quotientMetricSize hadd hsqrt x)] at h
  exact h

lemma quotientDistance_mul (x y x' y' : T.CauchyQuotient hadd) :
    T.quotientDistance hadd hsqrt (x*y) (x'*y') ≤
      ‖x‖^(2/3:ℝ)*T.quotientDistance hadd hsqrt y y'+
      ‖y'‖^(2/3:ℝ)*T.quotientDistance hadd hsqrt x x' := by
  have he : x*y-x'*y' = x*(y-y')+(x-x')*y' := by noncomm_ring
  change T.quotientMetricSize hadd hsqrt _ ≤ _
  rw [he]
  exact (T.quotientMetricSize_add hadd hsqrt _ _).trans (add_le_add
    (T.quotientMetricSize_mul_le_left hadd hsqrt _ _)
    (by
      have h := T.quotientMetricSize_mul_le_right hadd hsqrt (x-x') y'
      rw [mul_comm (T.quotientMetricSize hadd hsqrt (x-x')) (‖y'‖^(2/3:ℝ))] at h
      exact h))

lemma quotientDistance_star (x y : T.CauchyQuotient hadd) :
    T.quotientDistance hadd hsqrt (star x) (star y) = T.quotientDistance hadd hsqrt x y := by
  rw [quotientDistance,← star_sub,T.quotientMetricSize_star]; rfl
end CuntzPureness.PositiveQuasitrace

end

end OAI
