import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.CappedBilinearError

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal

theorem fractional_bilinear_tendsto_of_capped {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasure (μ j)] [IsFiniteMeasure ν]
    (hg : ∀ j, GlobalUpperGrowth (p + 1) C (μ j)) (hgν : GlobalUpperGrowth (p + 1) C ν)
    (w : ℕ → Ambient d → ℝ) (v : Ambient d → ℝ)
    (hw : ∀ j, Measurable (w j)) (hv : Measurable v)
    (hwI : ∀ j, Integrable (w j) (μ j)) (hvI : Integrable v ν)
    (henergy : ∀ j, Integrable
      (fun q : Ambient d × Ambient d => fractionalPairEnergy (p + 1) (w j) q.1 q.2)
      ((μ j).prod (μ j)))
    (henergyν : Integrable
      (fun q : Ambient d × Ambient d => fractionalPairEnergy (p + 1) v q.1 q.2) (ν.prod ν))
    (E M : ℝ)
    (hE : ∀ j, (∫ q : Ambient d × Ambient d,
      fractionalPairEnergy (p + 1) (w j) q.1 q.2 ∂(μ j).prod (μ j)) ≤ E)
    (hM : ∀ j, (μ j).real univ ≤ M)
    (φ : Ambient d → ℝ) (L B : ℝ≥0) (hφ : LipschitzWith L φ) (hB : ∀ x, |φ x| ≤ (B : ℝ))
    (hcapped : ∀ ε : ℝ, 0 < ε → Tendsto
      (fun j => ∫ q : Ambient d × Ambient d,
        (w j q.1 - w j q.2) * cappedTestKernel (p + 1) ε φ q ∂(μ j).prod (μ j)) atTop
      (𝓝 (∫ q : Ambient d × Ambient d,
        (v q.1 - v q.2) * cappedTestKernel (p + 1) ε φ q ∂ν.prod ν))) :
    Tendsto (fun j => ∫ q : Ambient d × Ambient d,
      fractionalBilinear (p + 1) (w j) φ q.1 q.2 ∂(μ j).prod (μ j)) atTop
      (𝓝 (∫ q : Ambient d × Ambient d, fractionalBilinear (p + 1) v φ q.1 q.2 ∂ν.prod ν)) := by
  apply Metric.tendsto_nhds.mpr
  intro η hη
  have hthird : 0 < η / 3 := by positivity
  obtain ⟨δ, hδ, hsmall⟩ := near_fractionalBilinear_uniformly_small p C μ hg w hw henergy
    E M hE hM φ L hφ (η / 3) hthird
  obtain ⟨δν, hδν, hsmallν⟩ := near_fractionalBilinear_uniformly_small p C
    (fun _ : ℕ => ν) (fun _ => hgν) (fun _ : ℕ => v) (fun _ => hv) (fun _ => henergyν)
    (∫ q : Ambient d × Ambient d, fractionalPairEnergy (p + 1) v q.1 q.2 ∂ν.prod ν)
    (ν.real univ) (fun _ => le_rfl) (fun _ => le_rfl) φ L hφ (η / 3) hthird
  let ε := min δ δν / 2
  have hε : 0 < ε := half_pos (lt_min hδ hδν)
  have hεδ : ε < δ := by dsimp only [ε]; linarith [min_le_left δ δν, lt_min hδ hδν]
  have hεδν : ε < δν := by dsimp only [ε]; linarith [min_le_right δ δν, lt_min hδ hδν]
  filter_upwards [Metric.tendsto_nhds.mp (hcapped ε hε) (η / 3) hthird] with j hj
  have hjerr : dist
      (∫ q : Ambient d × Ambient d, fractionalBilinear (p + 1) (w j) φ q.1 q.2 ∂(μ j).prod (μ j))
      (∫ q : Ambient d × Ambient d, (w j q.1 - w j q.2) * cappedTestKernel (p + 1) ε φ q
        ∂(μ j).prod (μ j)) < η / 3 := by
    rw [Real.dist_eq]
    exact (fractional_bilinear_integrable_and_cap_error p C (μ j) (hg j) (w j) φ
      (hw j) (hwI j) L B hφ hB (henergy j) ε hε).2.trans_lt (hsmall j ε hε hεδ)
  have hνerr : dist
      (∫ q : Ambient d × Ambient d, (v q.1 - v q.2) * cappedTestKernel (p + 1) ε φ q ∂ν.prod ν)
      (∫ q : Ambient d × Ambient d, fractionalBilinear (p + 1) v φ q.1 q.2 ∂ν.prod ν) < η / 3 := by
    rw [Real.dist_eq, abs_sub_comm]
    exact (fractional_bilinear_integrable_and_cap_error p C ν hgν v φ hv hvI
      L B hφ hB henergyν ε hε).2.trans_lt (hsmallν 0 ε hε hεδν)
  have htriangle := dist_triangle
    (∫ q : Ambient d × Ambient d, fractionalBilinear (p + 1) (w j) φ q.1 q.2 ∂(μ j).prod (μ j))
    (∫ q : Ambient d × Ambient d, (w j q.1 - w j q.2) * cappedTestKernel (p + 1) ε φ q
      ∂(μ j).prod (μ j))
    (∫ q : Ambient d × Ambient d, fractionalBilinear (p + 1) v φ q.1 q.2 ∂ν.prod ν)
  have htriangle' := dist_triangle
    (∫ q : Ambient d × Ambient d, (w j q.1 - w j q.2) * cappedTestKernel (p + 1) ε φ q
      ∂(μ j).prod (μ j))
    (∫ q : Ambient d × Ambient d, (v q.1 - v q.2) * cappedTestKernel (p + 1) ε φ q ∂ν.prod ν)
    (∫ q : Ambient d × Ambient d, fractionalBilinear (p + 1) v φ q.1 q.2 ∂ν.prod ν)
  linarith

end

end RieszRectifiability

end OAI
