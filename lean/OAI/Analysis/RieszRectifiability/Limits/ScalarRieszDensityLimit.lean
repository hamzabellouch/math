import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.ScalarRieszSpatialDomination
import OAI.Analysis.RieszRectifiability.Limits.ScalarRieszTestLimit

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap Metric Filter Topology Set

theorem scalarCappedTransform_density_integral_tendsto (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient (p + 1))) (hμ : GlobalUpperGrowth (p + 1) C μ)
    (e a : Ambient (p + 1)) (H : ℝ) (hH : 0 < H)
    (g : 𝓢(Ambient (p + 1), ℝ)) (hmean : (∫ y, g y) = 0)
    (hgs : ∀ y, g y ≠ 0 → dist y a ≤ H)
    (f : Ambient (p + 1) → ℝ) (hfm : Measurable f)
    (M : ℝ) (hfb : ∀ y, |f y| ≤ M)
    (ε : ℕ → ℝ) (hεpos : ∀ j, 0 < ε j) (hε : Tendsto ε atTop (𝓝 0)) :
    Integrable (fun y => f y * scalarRieszSchwartzTest (p + 1) e g y) μ ∧
      Tendsto (fun j => ∫ y, f y * scalarCappedTransform (p + 1) volume e (ε j) g y ∂μ)
        atTop (𝓝 (∫ y, f y * scalarRieszSchwartzTest (p + 1) e g y ∂μ)) := by
  obtain ⟨D, _, hDI, _, hDb⟩ :=
    exists_integrable_scalarCappedTransform_dominator p C μ hμ e a H hH g hmean hgs
  have hM : 0 ≤ M := (abs_nonneg (f 0)).trans (hfb 0)
  have hsmall : ∀ᶠ j in atTop, ε j ≤ H :=
    (hε.eventually (gt_mem_nhds hH)).mono fun _ h => h.le
  have hmeas (j : ℕ) : AEStronglyMeasurable
      (fun y => f y * scalarCappedTransform (p + 1) volume e (ε j) g y) μ :=
    hfm.aestronglyMeasurable.mul (scalarCappedTransform_continuous (p + 1) volume e
      (ε j) (hεpos j) g g.continuous.measurable g.integrable).aestronglyMeasurable
  have hbound (j : ℕ) (hj : ε j ≤ H) (y : Ambient (p + 1)) :
      ‖f y * scalarCappedTransform (p + 1) volume e (ε j) g y‖ ≤ M * D y := by
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul (hfb y) (hDb (ε j) (hεpos j) hj y) (norm_nonneg _) hM
  have hlim (y : Ambient (p + 1)) :
      Tendsto (fun j => f y * scalarCappedTransform (p + 1) volume e (ε j) g y) atTop
        (𝓝 (f y * scalarRieszSchwartzTest (p + 1) e g y)) :=
    (scalarCappedTransform_tendsto_schwartz p e g y ε hεpos hε).const_mul (f y)
  have hfm' : AEStronglyMeasurable (fun y => f y * scalarRieszSchwartzTest (p + 1) e g y) μ :=
    aestronglyMeasurable_of_tendsto_ae atTop hmeas (Eventually.of_forall hlim)
  have hI : Integrable (fun y => f y * scalarRieszSchwartzTest (p + 1) e g y) μ := by
    apply (hDI.const_mul M).mono' hfm'
    apply Eventually.of_forall
    intro y
    exact le_of_tendsto (hlim y).norm (hsmall.mono fun j hj => hbound j hj y)
  refine ⟨hI, ?_⟩
  exact tendsto_integral_filter_of_dominated_convergence (fun y => M * D y)
    (Eventually.of_forall hmeas)
    (hsmall.mono fun j hj => Eventually.of_forall (hbound j hj))
    (hDI.const_mul M) (Eventually.of_forall hlim)

end

end RieszRectifiability

end OAI
