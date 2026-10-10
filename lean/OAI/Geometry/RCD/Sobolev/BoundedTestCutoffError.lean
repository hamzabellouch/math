import OAI.Geometry.RCD.Metric.MeasuredBallLaw
import OAI.Geometry.RCD.Sobolev.NestedBallCutoff

namespace OAI

/-! # The exact mass deficit controls bounded test localization -/

open Set Metric Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]

theorem bounded_test_cutoff_error (μ : Measure X) [IsFiniteMeasure μ]
    {s : Set X} (hs : MeasurableSet s) (φ χ : X →ᵇ ℝ)
    (hχ : ∀ x, 0≤χ x ∧ χ x≤1) (hχ0 : ∀ x, x∉s → χ x=0) :
    |(∫ x in s, φ x ∂μ)-(∫ x, χ x*φ x ∂μ)|≤
      ‖φ‖*(μ.real s-(∫ x, χ x ∂μ)) := by
  let I : X → ℝ := s.indicator (fun _ => 1)
  have hI : Integrable I μ := (integrable_const (1:ℝ)).indicator hs
  have hφ := φ.integrable (μ := μ)
  have hp := (χ*φ).integrable (μ := μ)
  have hd : ∀ x, 0≤I x-χ x := by
    intro x
    by_cases hx : x∈s
    · simpa only [I,indicator_of_mem hx] using sub_nonneg.mpr (hχ x).2
    · simp only [I,indicator_of_notMem hx,hχ0 x hx,sub_self,le_refl]
  have hpoint : ∀ x, ‖s.indicator (fun x => φ x) x-χ x*φ x‖≤‖φ‖*(I x-χ x) := by
    intro x
    have he : s.indicator (fun x => φ x) x-χ x*φ x=(I x-χ x)*φ x := by
      by_cases hx : x∈s
      · simp only [I,indicator_of_mem hx]; ring
      · simp only [I,indicator_of_notMem hx,zero_sub,neg_mul]
    rw [he,norm_mul,Real.norm_eq_abs,abs_of_nonneg (hd x),mul_comm]
    exact mul_le_mul_of_nonneg_right (φ.norm_coe_le_norm x) (hd x)
  have hi := (norm_integral_le_integral_norm
    (s.indicator (fun x => φ x)-(fun x => χ x*φ x))).trans
    (integral_mono_ae ((hφ.indicator hs).sub hp).norm
      ((hI.sub (χ.integrable (μ := μ))).const_mul ‖φ‖)
      (Eventually.of_forall hpoint))
  change ‖∫ x, s.indicator (fun x => φ x) x-χ x*φ x ∂μ‖≤
    ∫ x, ‖φ‖*(I x-χ x) ∂μ at hi
  have hp' : Integrable (fun x => χ x*φ x) μ := hp
  rw [integral_sub (hφ.indicator hs) hp',integral_indicator hs,
    integral_const_mul,integral_sub hI (χ.integrable (μ := μ))] at hi
  simpa only [I,integral_indicator hs,setIntegral_const,smul_eq_mul,mul_one,
    Real.norm_eq_abs] using hi

end RegularPointCoordinates

end

end OAI
