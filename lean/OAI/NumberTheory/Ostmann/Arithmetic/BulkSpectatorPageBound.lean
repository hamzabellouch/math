import OAI.NumberTheory.Ostmann.Arithmetic.BulkResiduePageBound
import OAI.NumberTheory.Ostmann.Construction.NormalizedSpectatorComparison

namespace OAI

/-! # The actual normalized spectator gain used in the bulk Page average -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

/-- The numerical quartet estimate gives the local hypothesis of
`bulk_residue_page_bound`, for the actual balanced residue transform. -/
theorem normalized_bulk_spectator_mean_le {p : ℕ} [Fact p.Prime]
    (hp : 3 ≤ p) (n m : ℕ) (hm : 0 < m)
    (e : Equiv.Perm (TreeLeafIndex (n + 2) × Fin m))
    (hgood : 4 * Fintype.card (arrangementGraph m e).ConnectedComponent ≤
      3 * Fintype.card (TreeLeafIndex (n + 2)))
    (S : Finset (ZMod p)) (hlo : (1 / 3 : ℝ) ≤ residueDensity S)
    (hhi : residueDensity S ≤ 2 / 3) (hS : S.Nonempty) (hSp : S.card < p)
    (β ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hprincipal : 3 / Real.sqrt (p : ℝ) ≤ ε) (hβ : 2 * β ≤ ε)
    (hbias : ∀ (χ : MulChar (ZMod p) ℂ), χ ≠ 1 → ∀ a : ZMod p,
      ‖(S.card : ℂ)⁻¹ * ∑ x ∈ S, χ⁻¹ (-a - x)‖ ≤ β)
    (d₁ d₂ : SpectatorDiagram p (n + 2)) (cL cR : TreeLeafIndex n → Bool)
    (hconj : ∀ j, quartetBlockEquiv Bool n d₁.conjugations j =
      ((cL j, !(cL j)), (cR j, !(cR j))))
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hnum : quartetTreeConstant n * (ε ^ 2 + Real.sqrt (3 / (p : ℝ))) ≤ δ ^ 2) :
    ‖(Fintype.card (TreeLeafIndex (n + 2) × Fin m → (ZMod p)ˣ) : ℂ)⁻¹ *
      (∑ x : TreeLeafIndex (n + 2) × Fin m → (ZMod p)ˣ,
        d₁.bulkValue (normalizedResidueTransform S) x *
          conj (d₂.bulkValue (normalizedResidueTransform S) (x ∘ e.symm)))‖ ≤ δ := by
  apply (sq_le_sq₀ (norm_nonneg _) hδ).mp
  exact (normalized_spectator_bulk_comparison hp n m hm e hgood S hlo hhi hS hSp
    β ε hε hε1 hprincipal hβ hbias d₁ d₂ cL cR hconj).trans hnum

end Ostmann

end OAI
