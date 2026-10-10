import OAI.Analysis.KadisonKastler.PublishedBorelSelection

namespace OAI

/-! # Selecting measurable implementer fields

The input is the published Borel uniformization theorem. The conjugacy
relation, its Borel structure, and the strong measurability of the
selected operator and adjoint evaluations are proved locally.
-/

namespace KadisonKastler

open MeasureTheory TopologicalSpace

noncomputable section

universe u v

variable {X : Type u} [MeasurableSpace X] [StandardBorelSpace X]
  {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [SeparableSpace H] [MeasurableSpace H] [BorelSpace H]

theorem exists_measurable_implementer_field
    (hpub : PublishedUnitaryBorelSelection.{u, v}) (μ : Measure X) [IsFiniteMeasure μ]
    (M N : X → VonNeumannAlgebra H)
    (A : ∀ p, StrongUnitBallTestSequence (M p)) (B : ∀ p, StrongUnitBallTestSequence (N p))
    (hA : ∀ j x, Measurable (fun p => (A p).op j x))
    (hB : ∀ j x, Measurable (fun p => (B p).op j x))
    {a : ℝ} (ha : 0 ≤ a)
    (hex : ∀ᵐ p ∂μ, ∃ u : unitary (H →L[ℂ] H),
      Conjugates u (M p) (N p) ∧ ‖(u : H →L[ℂ] H) - 1‖ ≤ a) :
    ∃ U : X → unitary (H →L[ℂ] H),
      (∀ x, AEStronglyMeasurable (fun p => (U p : H →L[ℂ] H) x) μ) ∧
      (∀ x, AEStronglyMeasurable (fun p => (star (U p) : H →L[ℂ] H) x) μ) ∧
      ∀ᵐ p ∂μ, Conjugates (U p) (M p) (N p) ∧ ‖(U p : H →L[ℂ] H) - 1‖ ≤ a := by
  obtain ⟨ξ, hξ⟩ := exists_dense_seq (α := H)
  have : PolishSpace (StrongUnitarySpace ξ) := strongUnitarySpace_polish ξ hξ
  let R : Set (X × StrongUnitarySpace ξ) := {p |
    Conjugates (decodeStrongUnitary ξ p.2) (M p.1) (N p.1) ∧
    ‖(decodeStrongUnitary ξ p.2 : H →L[ℂ] H) - 1‖ ≤ a}
  have hR : MeasurableSet R :=
    measurableSet_bounded_implementer_relation M N A B hA hB ξ hξ ha
  have hne : ∀ᵐ p ∂μ, ∃ q : StrongUnitarySpace ξ, (p, q) ∈ R := by
    filter_upwards [hex] with p hp
    obtain ⟨u, hu⟩ := hp
    refine ⟨encodeStrongUnitary ξ u, ?_⟩
    change Conjugates (decodeStrongUnitary ξ (encodeStrongUnitary ξ u)) (M p) (N p) ∧ _
    simpa only [decode_encodeStrongUnitary ξ hξ] using hu
  obtain ⟨f, hf, hrel⟩ := hpub X H ξ hξ μ R hR hne
  refine ⟨fun p => decodeStrongUnitary ξ (f p), ?_, ?_, hrel⟩
  · intro x
    exact ((continuous_decodeStrongUnitary_apply ξ hξ x).measurable.comp_aemeasurable hf).aestronglyMeasurable
  · intro x
    exact ((continuous_star_decodeStrongUnitary_apply ξ hξ x).measurable.comp_aemeasurable hf).aestronglyMeasurable

end

end KadisonKastler

end OAI
