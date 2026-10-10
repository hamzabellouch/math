import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.MulBounded

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set
open scoped NNReal
open scoped Topology ENNReal NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
variable {X : Type*} [MetricSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X]
  [MeasurableSpace X] [BorelSpace X] {m : Measure X}

lemma IsLocalWeakUpperGradient.comp_contDiff {f D : X → ℝ}
    (hD : IsLocalWeakUpperGradient m f D) (hf : AEMeasurable f m)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) {B : ℝ}
    (hB : ∀ᵐ x ∂m, |deriv φ (f x)| ≤ B) :
    IsLocalWeakUpperGradient m (φ ∘ f) (fun x => |deriv φ (f x)| * D x) := by
  have hm : AEMeasurable (fun x => |deriv φ (f x)|) m :=
    ((hφ.continuous_deriv le_rfl).measurable.comp_aemeasurable hf).abs
  refine ⟨?_,?_,?_⟩
  · simpa only [mul_comm] using hD.1.mul_bounded hm.aestronglyMeasurable
      (by simpa only [abs_abs] using hB)
  · filter_upwards [hD.2.1] with x hx
    exact mul_nonneg (abs_nonneg _) hx
  · intro π hπ hb
    apply lintegral_mono_ae
    filter_upwards [hD.ae_exists_ac_representative hf hπ hb] with γ hγ
    obtain ⟨q,hq,hq0,hq1,heq,hder⟩ := hγ
    have hp := ac_comp_contDiff hq hφ
    have hder' : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1),
        ENNReal.ofReal |deriv (φ ∘ q) t| ≤
          ENNReal.ofReal (|deriv φ (f (evalReal γ t))| * D (evalReal γ t)) *
            metricSpeed γ t := by
      filter_upwards [heq,hder, ae_restrict_of_ae hq.ae_differentiableAt,
        ae_restrict_mem measurableSet_Icc] with t ht hd hqd htm
      have htt : t ∈ uIcc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using htm
      rw [deriv_comp t (hφ.differentiable (by simp) (q t)) (hqd htt), abs_mul,
        ENNReal.ofReal_mul (abs_nonneg _), ht,
        ENNReal.ofReal_mul (abs_nonneg _), mul_assoc]
      exact mul_le_mul' le_rfl hd
    calc
      ENNReal.ofReal |(φ ∘ f) (γ timeOne) - (φ ∘ f) (γ timeZero)| =
          ‖∫ t in Icc (0 : ℝ) 1, deriv (φ ∘ q) t‖ₑ := by
        rw [← ofReal_norm, Real.norm_eq_abs, integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le zero_le_one, hp.integral_deriv_eq_sub]
        simp only [Function.comp_apply, hq0, hq1]
      _ ≤ ∫⁻ t in Icc (0 : ℝ) 1, ‖deriv (φ ∘ q) t‖ₑ := enorm_integral_le_lintegral_enorm _
      _ ≤ _ := lintegral_mono_ae (by simpa only [Real.enorm_eq_ofReal_abs] using hder')

lemma IsLocalWeakUpperGradient.exp {f D : X → ℝ}
    (hD : IsLocalWeakUpperGradient m f D) (hf : AEMeasurable f m) {B : ℝ}
    (hB : ∀ᵐ x ∂m, f x ≤ B) :
    IsLocalWeakUpperGradient m (fun x => Real.exp (f x))
      (fun x => Real.exp (f x) * D x) := by
  have hb : ∀ᵐ x ∂m, |deriv Real.exp (f x)| ≤ Real.exp B := by
    filter_upwards [hB] with x hx
    simp only [Real.deriv_exp, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr hx
  simpa only [Function.comp_def, Real.deriv_exp, abs_of_pos (Real.exp_pos _)] using
    hD.comp_contDiff hf Real.contDiff_exp hb

end WeakHessian

end
end InlinedFile0

end OAI
