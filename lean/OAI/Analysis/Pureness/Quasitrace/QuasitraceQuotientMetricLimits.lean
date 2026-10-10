import OAI.Analysis.Pureness.Quasitrace.QuasitraceQuotientMetricOperations
import OAI.Analysis.Pureness.Quasitrace.QuasitraceQuotientNormContinuity
import OAI.Analysis.Pureness.Quasitrace.QuasitraceQuotientBoundedLimits

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace Filter
open scoped Topology NNReal ENNReal ComplexOrder
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]
variable (T : CuntzPureness.PositiveQuasitrace D)
variable (hadd : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)
variable (hsqrt : ∀ a b : Positive D, Real.sqrt (T (Positive.add a b)) ≤ Real.sqrt (T a)+Real.sqrt (T b))

lemma quotientMetricSize_norm_continuous : Continuous (T.quotientMetricSize hadd hsqrt) := by
  exact (Real.continuous_rpow_const (show 0 ≤ (3:ℝ)⁻¹ by positivity)).comp
    (Complex.continuous_re.comp ((T.quotientValue_norm_continuous hadd hsqrt).comp
      (continuous_star.mul continuous_id)))

lemma quotient_norm_limit_is_metric_limit {u : ℕ → T.CauchyQuotient hadd} {x : T.CauchyQuotient hadd}
    (hu : Tendsto u atTop (nhds x)) :
    Tendsto (fun n => T.quotientDistance hadd hsqrt (u n) x) atTop (nhds 0) := by
  have h := (T.quotientMetricSize_norm_continuous hadd hsqrt).tendsto 0
  have he : Tendsto (fun n => u n-x) atTop (nhds 0) := by simpa only [sub_self] using hu.sub_const x
  simpa only [Function.comp_def,quotientDistance,T.quotientMetricSize_zero] using h.comp he

lemma quotient_metric_limit_mul {u v : ℕ → T.CauchyQuotient hadd} {x y : T.CauchyQuotient hadd}
    (hu : Tendsto (fun n => T.quotientDistance hadd hsqrt (u n) x) atTop (nhds 0))
    (hv : Tendsto (fun n => T.quotientDistance hadd hsqrt (v n) y) atTop (nhds 0))
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ n, ‖u n‖ ≤ C) :
    Tendsto (fun n => T.quotientDistance hadd hsqrt (u n*v n) (x*y)) atTop (nhds 0) := by
  have ht := (hv.const_mul (C^(2/3:ℝ))).add (hu.const_mul (‖y‖^(2/3:ℝ)))
  simp only [mul_zero,add_zero] at ht
  apply squeeze_zero (fun n => T.quotientDistance_nonneg hadd hsqrt _ _) _ ht
  intro n
  exact (T.quotientDistance_mul hadd hsqrt (u n) (v n) x y).trans
    (add_le_add (mul_le_mul_of_nonneg_right
      ((Real.rpow_le_rpow_iff (norm_nonneg _) hC (by norm_num : (0:ℝ) < 2/3)).2 (hb n))
      (T.quotientDistance_nonneg hadd hsqrt _ _)) le_rfl)

lemma quotient_metric_limit_star {u : ℕ → T.CauchyQuotient hadd} {x : T.CauchyQuotient hadd}
    (hu : Tendsto (fun n => T.quotientDistance hadd hsqrt (u n) x) atTop (nhds 0)) :
    Tendsto (fun n => T.quotientDistance hadd hsqrt (star (u n)) (star x)) atTop (nhds 0) := by
  simpa only [T.quotientDistance_star] using hu

lemma quotient_metric_limit_selfAdjoint {u : ℕ → T.CauchyQuotient hadd} {x : T.CauchyQuotient hadd}
    (hu : Tendsto (fun n => T.quotientDistance hadd hsqrt (u n) x) atTop (nhds 0))
    (hsa : ∀ n, IsSelfAdjoint (u n)) : IsSelfAdjoint x := by
  have hs := T.quotient_metric_limit_star hadd hsqrt hu
  simp only [(hsa _).star_eq] at hs
  exact T.quotient_metric_limit_unique hadd hsqrt u (star x) x hs hu
end CuntzPureness.PositiveQuasitrace

end

end OAI
