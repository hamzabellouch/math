import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.BoundedBoxHeight
import OAI.Analysis.RieszRectifiability.Projections.GlobalProjectionLimit

namespace OAI

namespace RieszRectifiability

noncomputable section

open BoxIntegral MeasureTheory Metric Set Function Filter Topology
open scoped NNReal ENNReal

theorem exists_bounded_global_projection_height {ι : Type*} [Fintype ι] {d : ℕ}
    (e : (ι → ℝ) → Ambient d) (π : Ambient d → ι → ℝ)
    (K Q : ℝ≥0) (he : LipschitzWith K e) (hπ : LipschitzWith Q π) (hleft : LeftInverse π e)
    (σ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (σ j)]
    (hlocal : CompactTestConvergence σ (coordinatePlaneMeasure e))
    (C : ℝ) (hC : 0 < C)
    (hlower : ∀ j x, x ∈ (σ j).support → ∀ r : ℝ, AdmissibleRadius (σ j) r →
      ENNReal.ofReal (r ^ Fintype.card ι / C) ≤ (σ j) (ball x r))
    (hdiam : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ENNReal.ofReal r ≤ ediam (σ j).support)
    (w : ℕ → Ambient d → ℝ)
    (hw : ∀ H j, MemLp (w j) 2 ((σ j).restrict (boundedProjectionRegion π (e 0) K H)))
    (B E : ℕ → ℝ)
    (hB : ∀ H j, (∫ x, w j x ^ 2 ∂(σ j).restrict (boundedProjectionRegion π (e 0) K H)) ≤ B H)
    (henergy : ∀ H j, Integrable
      (fun q : Ambient d × Ambient d => fractionalPairEnergy (Fintype.card ι) (w j) q.1 q.2)
      (((σ j).restrict (boundedProjectionRegion π (e 0) K H)).prod
        ((σ j).restrict (boundedProjectionRegion π (e 0) K H))))
    (hE : ∀ H j, (∫ q : Ambient d × Ambient d,
      fractionalPairEnergy (Fintype.card ι) (w j) q.1 q.2
      ∂(((σ j).restrict (boundedProjectionRegion π (e 0) K H)).prod
        ((σ j).restrict (boundedProjectionRegion π (e 0) K H)))) ≤ E H) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : Ambient d → ℝ, Measurable f ∧
      (∀ H, MemLp f 2 ((coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H))) ∧
      (∀ H, Tendsto (fun j => ∫ x, w (φ j) x ^ 2
        ∂(σ (φ j)).restrict (boundedProjectionRegion π (e 0) K H)) atTop
        (𝓝 (∫ x, f x ^ 2 ∂(coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H)))) ∧
      ∀ H (ψ : Ambient d → ℝ) (L A : ℝ≥0), HasCompactSupport ψ →
        LipschitzWith L ψ → (∀ x, |ψ x| ≤ (A : ℝ)) →
        Tendsto (fun j => ∫ x, w (φ j) x * ψ x
          ∂(σ (φ j)).restrict (boundedProjectionRegion π (e 0) K H)) atTop
          (𝓝 (∫ x, f x * ψ x
            ∂(coordinatePlaneMeasure e).restrict (boundedProjectionRegion π (e 0) K H))) := by
  exact exists_global_projection_height (exhaustionBox ι) e π K Q he hπ hleft σ
    (boundedProjectionRegion π (e 0) K)
    (fun H => boundedProjectionRegion_isOpen π hπ.continuous (e 0) K H)
    (boundedProjectionRegion_cover π (e 0) K)
    (fun H j => boundedProjectionFiniteMeasure (σ j) π (e 0) K H)
    (fun _ _ => rfl)
    (coordinatePlaneMeasure_restrict_boundedRegion e π K he hπ.continuous hleft)
    (boundedProjectionFiniteMeasure_tendsto e π K Q he hπ hleft σ hlocal)
    (fun H j => boundedProjectionRegion_ae_coordinates (σ j) π hπ.continuous (e 0) K H)
    (boundedProjectionFiniteMeasure_height_of_AD_lower e π K Q he hπ hleft σ hlocal C hC hlower hdiam)
    w hw B E hB henergy hE

end

end RieszRectifiability

end OAI
