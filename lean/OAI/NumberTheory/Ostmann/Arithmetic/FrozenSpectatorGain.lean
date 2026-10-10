import OAI.NumberTheory.Ostmann.Arithmetic.FrozenSpectatorAverage
import OAI.NumberTheory.Ostmann.Construction.SignedBulkGain

namespace OAI

namespace Ostmann
open scoped Classical BigOperators

/-- The tolerance and threshold depend only on the fixed depth and the
requested exponential saving. All base values, sample trees, matchings and
bulk lengths remain variable. -/
theorem exists_frozenSpectatorGain (n : ℕ) (C D : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ N : ℕ, 3 ≤ N ∧
      ∀ (q : ℕ) [Fact q.Prime], N ≤ q →
      ∀ (σ : Type*) (base : σ → ℕ) (m : ℕ), 0 < m →
      ∀ (t : Bool → FrequencyTree ℤ (n + 2))
        (small : Bool → TreeLeafTuple (List σ) (n + 2))
        (samples : Bool → MovingSampleSlots σ (n + 2)),
      (∀ b, movingGiantFrequencyUnits q (n + 2) (t b)) →
      (∀ b, ((treeLeafProduct (n + 2) (movingSlotValues base (n + 2) (small b)) : ℕ) :
        ZMod q) ≠ 0) →
      (∀ b, ((samples b).values base).UnitsAt q) →
      ∀ (twist : Bool → (ZMod q)ˣ) (e : Equiv.Perm (TreeLeafIndex (n + 2) × Fin m)),
      4 * Fintype.card (arrangementGraph m e).ConnectedComponent ≤
        3 * Fintype.card (TreeLeafIndex (n + 2)) →
      ∀ (S : Finset (ZMod q)), (1 / 3 : ℝ) ≤ residueDensity S →
      residueDensity S ≤ 2 / 3 → S.Nonempty → S.card < q →
      ∀ β : ℝ, 2 * β ≤ ε →
      (∀ (χ : MulChar (ZMod q) ℂ), χ ≠ 1 → ∀ a : ZMod q,
        ‖(S.card : ℂ)⁻¹ * ∑ x ∈ S, χ⁻¹ (-a - x)‖ ≤ β) →
      ‖(Fintype.card (TreeLeafIndex (n + 2) × Fin m → (ZMod q)ˣ) : ℂ)⁻¹ *
        ∑ z, frozenBulkSpectatorHaar base (n + 2) m t small samples twist e
          (normalizedResidueTransform S) z‖ ≤ signedBulkGainTarget (n + 2) C D := by
  obtain ⟨ε, hε, hε1, N, hN, hnum⟩ := exists_signedBulkGain_parameters n C D
  refine ⟨ε, hε, hε1, N, hN, ?_⟩
  intro q hq hqN σ base m hm t small samples hfreq hsmall hsamples twist e hgood S hlo hhi hS hSq β hβ hbias
  exact frozenBulkSpectatorHaar_mean_le (hN.trans hqN) base n m hm t small samples
    hfreq hsmall hsamples twist e hgood S hlo hhi hS hSq β ε hε.le hε1
    (hnum q hqN).1 hβ hbias (signedBulkGainTarget (n + 2) C D)
    (signedBulkGainTarget_pos _ _ _).le (hnum q hqN).2

end Ostmann

end OAI
