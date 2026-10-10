import OAI.Analysis.KadisonKastler.MeasurableProductCocycle
import OAI.Analysis.KadisonKastler.MeasurableBoundaryIntertwiner

namespace OAI

/-! # The measurable product intertwiner in common tracial position -/

namespace KadisonKastler

open MeasureTheory
open scoped BoundedContinuousFunction

noncomputable section

variable {G D H : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace D] {μ : Measure D} [IsFiniteMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M N : VonNeumannAlgebra H}

/-- The two commuting boundary actions have a measurable unitary
intertwiner close to the identity, using the actual product mean. -/
theorem exists_product_boundary_intertwiner
    (pM : StandardTracialPosition M) (pN : StandardTracialPosition N)
    (α : NonsingularAction G D μ) (m₂ : ScalarBoundaryMean α.prod)
    (hTom : PublishedFieldTomiyama (G := G × G) (H := H) (μ := μ.prod μ))
    (U : G →* unitary (Algebra M)) (W : G → D → unitary (H →L[ℂ] H))
    (hW : ∀ g ξ, AEStronglyMeasurable (fun x => (W g x : H →L[ℂ] H) ξ) μ)
    (hWN : ∀ g, ∀ᵐ x ∂μ, (W g x : H →L[ℂ] H) ∈ N)
    (hc : ∀ g h, ∀ᵐ x ∂μ,
      (W g x : H →L[ℂ] H) * W h (α.toPerm g⁻¹ x) = W (g * h) x)
    {δ κ : ℝ} (hδ : 0 ≤ δ) (hκ : 0 ≤ κ) (hsmall : 2 * δ + 2 * κ < 1)
    (hclose : ∀ g, ∀ᵐ x ∂μ,
      ‖(W g x : H →L[ℂ] H) - (U g : Algebra M).val‖ ≤ δ)
    (hJ : ‖(pM.conjugation : H →L⋆[ℂ] H) -
      (pN.conjugation : H →L⋆[ℂ] H)‖ ≤ κ) :
    ∃ L : D × D → unitary (H →L[ℂ] H),
      (∀ ξ, AEStronglyMeasurable (fun x => (L x : H →L[ℂ] H) ξ) (μ.prod μ)) ∧
      (∀ᵐ x ∂μ.prod μ, ‖(L x : H →L[ℂ] H) - 1‖ ≤ 4 * δ + 4 * κ) ∧
      (∀ g, ∀ᵐ x ∂μ.prod μ,
        (L x : H →L[ℂ] H) * productBoundaryRepresentation pM U g =
          (productBoundaryValue pN W g x : H →L[ℂ] H) *
            L (α.prod.toPerm g⁻¹ x)) := by
  let S := productBoundaryClass pN W hW
  have hSc := productBoundaryClass_cocycle pN α W hW hWN hc
  have hSn := productBoundaryClass_close pM pN U W hW hδ hκ hclose hJ
  obtain ⟨L, hm, hn, hi⟩ := m₂.exists_measurable_boundary_intertwiner hTom S hSc
    (productBoundaryRepresentative pN W hW) (fun _ => rfl)
    (productBoundaryRepresentation pM U) hsmall (fun g =>
      ((S.val - (productBoundaryConstantFamily (μ := μ) pM U).val).norm_coe_le_norm g).trans hSn)
  refine ⟨L, hm, ?_, hi⟩
  filter_upwards [hn] with x hx
  linarith

end

end KadisonKastler

end OAI
