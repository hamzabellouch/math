import OAI.NumberTheory.Ostmann.Supply.CenteredSupportProjection
import OAI.NumberTheory.Ostmann.Characters.SparseTransformSpectrum

namespace OAI

/-! # Sparse projection of the actual normalized residue indicator -/

namespace Ostmann
open scoped Classical BigOperators

/-- The projection chosen in (5.7) kills constants and loses at most epsilon
squared of the normalized residue indicator's energy. -/
theorem sparse_residue_projection {p : ℕ} [Fact p.Prime]
    (S : Finset (ZMod p)) (hS : S.Nonempty) (hSp : S.card < p)
    (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hL1 : (p : ℝ)⁻¹ * ∑ b, ‖normalizedResidueTransform S b‖ ≤ ε ^ 2) :
    let E := largeTransformSpectrum (normalizedResidueTransform S)
    0 ∉ E ∧ (∀ b, -b ∈ E ↔ b ∈ E) ∧ (E.card : ℝ) ≤ ε * p ∧
      (∀ c x, finiteSpectralProjection E (fun _ => c) x = 0) ∧
      (1 - ε ^ 2) * p ≤ ∑ x, ‖finiteSpectralProjection E (normalizedResidueIndicator S) x‖ ^ 2 ∧
      (∑ x, ‖normalizedResidueIndicator S x -
        finiteSpectralProjection E (normalizedResidueIndicator S) x‖ ^ 2) ≤ ε ^ 2 * p := by
  intro E
  obtain ⟨hz, hn, hc, he⟩ := normalizedResidueTransform_sparse S hS hSp ε (ε ^ 2)
    (by nlinarith) le_rfl hL1
  refine ⟨hz, hn, hc, fun c x => finiteSpectralProjection_constant E hz c x, ?_, ?_⟩
  · simpa only [finiteSpectralProjection_energy, E, normalizedResidueTransform] using he
  · rw [finiteSpectralProjection_residual_energy,
      Finset.sum_sdiff_eq_sub (Finset.subset_univ E)]
    change (∑ b, ‖normalizedResidueTransform S b‖ ^ 2) -
      (∑ b ∈ E, ‖normalizedResidueTransform S b‖ ^ 2) ≤ _
    rw [normalizedResidueTransform_energy S hS hSp]
    linarith

end Ostmann

end OAI
