import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.LocallyIntegrable

namespace OAI

/-! # A finite quadratic tail gives a global weighted moment -/

open Set MeasureTheory Metric Filter
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {μ : Measure X} [IsFiniteMeasureOnCompacts μ]

theorem integrable_one_add_sq_of_tail {f : X → ℝ} (hf : Continuous f)
    (hf0 : ∀ x, 0 ≤ f x) (p : X) {R : ℝ} (hR : 0 < R)
    (htail : IntegrableOn (fun x => f x*(dist x p)^2) (ball p R)ᶜ μ) :
    Integrable (fun x => f x*(1+(dist x p)^2)) μ := by
  have hc : Continuous (fun x => f x*(1+(dist x p)^2)) := by fun_prop
  have hi : IntegrableOn (fun x => f x*(1+(dist x p)^2)) (ball p R) μ :=
    (hc.continuousOn.integrableOn_compact (isCompact_closedBall p R)).mono_set
    (ball_subset_closedBall : ball p R ⊆ closedBall p R)
  have ho : IntegrableOn (fun x => f x*(1+(dist x p)^2)) (ball p R)ᶜ μ := by
    apply (htail.const_mul ((R^2)⁻¹+1)).mono' hc.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_ball.compl] with x hx
    have hd : R ≤ dist x p := le_of_not_gt hx
    have hs : R^2 ≤ (dist x p)^2 := pow_le_pow_left₀ hR.le hd 2
    have hsq : 0 < R^2 := sq_pos_of_pos hR
    have hinv : (R^2)⁻¹*R^2 = 1 := inv_mul_cancel₀ hsq.ne'
    have hh := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hsq.le)
    rw [hinv] at hh
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hf0 x) (by positivity))]
    have hm := mul_le_mul_of_nonneg_left hh (hf0 x)
    nlinarith
  simpa only [union_compl_self,integrableOn_univ] using hi.union ho

end RegularPointCoordinates

end

end OAI
