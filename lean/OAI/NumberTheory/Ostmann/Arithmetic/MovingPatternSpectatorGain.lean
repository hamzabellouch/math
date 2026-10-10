import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternSpectatorUnits
import OAI.NumberTheory.Ostmann.Arithmetic.FrozenSpectatorNorm

namespace OAI

/-! # The quartet estimate for the actual equality-pattern spectator -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingPatternSpectatorHaar_mean_le {B C : Type*} {N q n m : ℕ} [Fact q.Prime]
    (e : Fin (N + 1) ≃ B ⊕ C) (base : Fin (N + 1) → ℕ)
    (t : Bool → FrequencyTree ℤ (n + 2))
    (small : Bool → TreeLeafTuple (List B) (n + 2))
    (pattern : Bool × MovingSampleIndex (n + 2) → C)
    (hq : 3 ≤ q) (hm : 0 < m)
    (hfreq : ∀ b, ∀ s ∈ allFrequencyList (n + 2) (t b), s ≠ 0 ∧ s.natAbs < q)
    (hsmall : ∀ b, ∀ i ∈ flattenMovingSlots (n + 2) (small b),
      (base (e.symm (.inl i)) : ZMod q) ≠ 0)
    (hsamples : ∀ c, (base (e.symm (.inr c)) : ZMod q) ≠ 0)
    (twist : Bool → (ZMod q)ˣ) (perm : Equiv.Perm (TreeLeafIndex (n + 2) × Fin m))
    (hgood : 4 * Fintype.card (arrangementGraph m perm).ConnectedComponent ≤
      3 * Fintype.card (TreeLeafIndex (n + 2)))
    (S : Finset (ZMod q)) (hlo : (1 / 3 : ℝ) ≤ residueDensity S)
    (hhi : residueDensity S ≤ 2 / 3) (hS : S.Nonempty) (hSq : S.card < q)
    (β ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hprincipal : 3 / Real.sqrt (q : ℝ) ≤ ε) (hβ : 2 * β ≤ ε)
    (hbias : ∀ (χ : MulChar (ZMod q) ℂ), χ ≠ 1 → ∀ a : ZMod q,
      ‖(S.card : ℂ)⁻¹ * ∑ x ∈ S, χ⁻¹ (-a - x)‖ ≤ β)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hnum : quartetTreeConstant n * (ε ^ 2 + Real.sqrt (3 / (q : ℝ))) ≤ δ ^ 2) :
    ‖(Fintype.card (TreeLeafIndex (n + 2) × Fin m → (ZMod q)ˣ) : ℂ)⁻¹ *
      ∑ z, frozenBulkSpectatorHaar base (n + 2) m t
        (fun b => movingPatternFiniteSmall e (n + 2) (small b))
        (movingPatternFiniteSamples e (n + 2) pattern) twist perm (normalizedResidueTransform S) z‖ ≤ δ := by
  exact frozenBulkSpectatorHaar_mean_le hq base n m hm t _ _
    (fun b => movingGiantFrequencyUnits_of_bounds (t b) (hfreq b))
    (fun b => movingPatternFiniteSmall_unit e base (small b) (hsmall b))
    (movingPatternFiniteSamples_units e base pattern hsamples)
    twist perm hgood S hlo hhi hS hSq β ε hε hε1 hprincipal hβ hbias δ hδ hnum

end Ostmann

end OAI
