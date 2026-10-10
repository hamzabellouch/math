import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.SmoothAnnularLimitBounds
import OAI.Analysis.RieszRectifiability.Foundations.SmoothAnnularRescaling

namespace OAI

/-!
# Smooth annular bounds on tangent measures

Local bounds near the blowup center pass to every support point of a tangent measure.
Support approximants rescale into the original neighborhood, while their outer annular
radii shrink below the prescribed cap, allowing the moving-center limit bound to apply.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology

theorem smoothAnnularTransform_bound_on_tangent {d : ℕ} (n : ℕ) (G B cap : ℝ)
    (μ ν : Measure (Ambient d)) [IsFiniteMeasureOnCompacts ν]
    (hg : GlobalUpperGrowth n G μ) (U : Set (Ambient d)) (hU : IsOpen U)
    (a : Ambient d) (ha : a ∈ U) (hcap : 0 < cap)
    (s : ℕ → ℝ) (hs : ∀ j, 0 < s j) (hs0 : Tendsto s atTop (𝓝 0))
    (hlocal : CompactTestConvergence (fun j => blowupMeasure n μ a (s j)) ν)
    (hbound : ∀ x ∈ μ.support, x ∈ U → ∀ r R : ℝ, ∀ hr : 0 < r, ∀ hrR : r ≤ R,
      R < cap → ‖smoothAnnularTransform n μ x r R hr (hr.trans_le hrR)‖ ≤ B)
    (b : Ambient d) (hbs : b ∈ ν.support) (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R) :
    ‖smoothAnnularTransform n ν b r R hr (hr.trans_le hrR)‖ ≤ B := by
  let : ContinuousSMul ℝ (Ambient d) := IsBoundedSMul.continuousSMul
  let μj := fun j => blowupMeasure n μ a (s j)
  have hgj (j : ℕ) : GlobalUpperGrowth n G (μj j) :=
    blowupMeasure_growth n μ a (s j) G (hs j) hg
  let (j : ℕ) : IsFiniteMeasureOnCompacts (μj j) := globalGrowth_finite_on_compacts G (μj j) (hgj j)
  obtain ⟨φ, x, _, hφ, hxs, hx⟩ := compactTestConvergence_support_approximants μj ν hlocal b hbs
  have hscaled : Tendsto (fun j => a + s (φ j) • x j) atTop (𝓝 a) := by
    simpa only [zero_smul, add_zero] using!
      (tendsto_const_nhds (x := a)).add ((hs0.comp hφ).smul hx)
  have hscaledR : Tendsto (fun j => s (φ j) * R) atTop (𝓝 0) := by
    simpa only [zero_mul] using! (hs0.comp hφ).mul_const R
  have hc : CompactTestConvergence (μj ∘ φ) ν := fun f => (hlocal f).comp hφ
  apply smoothAnnularTransform_bound_of_center_limit n G B (μj ∘ φ) ν
    (fun j => hgj (φ j)) hc x b hx r R hr hrR
  filter_upwards [hscaled.eventually (hU.mem_nhds ha),
    hscaledR.eventually (gt_mem_nhds hcap)] with j hjU hjR
  have hsupport : a + s (φ j) • x j ∈ μ.support :=
    (blowupMeasure_support_iff n μ a (x j) (s (φ j)) (hs (φ j))).mp (hxs j)
  change ‖smoothAnnularTransform n (blowupMeasure n μ a (s (φ j))) (x j)
    r R hr (hr.trans_le hrR)‖ ≤ B
  rw [smoothAnnularTransform_blowup n μ a (x j) (s (φ j)) r R (hs (φ j)) hr (hr.trans_le hrR)]
  exact hbound _ hsupport hjU _ _ (mul_pos (hs (φ j)) hr)
    (mul_le_mul_of_nonneg_left hrR (hs (φ j)).le) hjR

end

end RieszRectifiability

end OAI
