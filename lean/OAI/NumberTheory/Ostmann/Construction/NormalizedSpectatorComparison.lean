import OAI.NumberTheory.Ostmann.Construction.SpectatorBulkComparison
import OAI.NumberTheory.Ostmann.Characters.NormalizedMixedFourier

namespace OAI

/-! # Applying the bulk comparison to the actual balanced residue supports -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem normalizedResidueTransform_mixed_le {p : ℕ} [Fact p.Prime]
    (S : Finset (ZMod p)) (hlo : (1 / 3 : ℝ) ≤ residueDensity S)
    (hhi : residueDensity S ≤ 2 / 3) (β ε : ℝ)
    (hprincipal : 3 / Real.sqrt (p : ℝ) ≤ ε) (hβ : 2 * β ≤ ε)
    (hbias : ∀ (χ : MulChar (ZMod p) ℂ), χ ≠ 1 → ∀ a : ZMod p,
      ‖(S.card : ℂ)⁻¹ * ∑ x ∈ S, χ⁻¹ (-a - x)‖ ≤ β) :
    MixedFourierBound (normalizedResidueTransform S) ε := by
  have h := normalizedResidueTransform_mixedBound S hlo hhi β hbias
  intro χ a
  exact (h χ a).trans (max_le hprincipal hβ)

theorem normalized_spectator_bulk_comparison {p : ℕ} [Fact p.Prime] (hp : 3 ≤ p)
    (n m : ℕ) (hm : 0 < m)
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
    (hconj : ∀ q, quartetBlockEquiv Bool n d₁.conjugations q =
      ((cL q, !(cL q)), (cR q, !(cR q)))) :
    ‖(Fintype.card (TreeLeafIndex (n + 2) × Fin m → (ZMod p)ˣ) : ℂ)⁻¹ *
      (∑ x : TreeLeafIndex (n + 2) × Fin m → (ZMod p)ˣ,
        d₁.bulkValue (normalizedResidueTransform S) x *
          conj (d₂.bulkValue (normalizedResidueTransform S) (x ∘ e.symm)))‖ ^ 2 ≤
      quartetTreeConstant n * (ε ^ 2 + Real.sqrt (3 / (p : ℝ))) := by
  exact spectator_bulk_comparison hp n m hm e hgood (normalizedResidueTransform S)
    (normalizedResidueTransform_zero S) (normalizedResidueTransform_energy S hS hSp).le
    ε hε hε1 (normalizedResidueTransform_mixed_le S hlo hhi β ε hprincipal hβ hbias)
    d₁ d₂ cL cR hconj

end Ostmann

end OAI
