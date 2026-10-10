import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternWindowGain
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSpectatorCost

namespace OAI

/-! # A window-uniform local tolerance for the literal prime comparison -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

/-- A single mixed-character tolerance and prime threshold work for all
actual pattern trees and bulk lengths. No local cancellation bound is an
assumption here: it is derived from the quartet theorem. -/
theorem exists_movingPatternPrimeGain_window (ψ : 𝓢(ℝ, ℂ)) (n r₀ : ℕ)
    (A H B D F gain : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H) :
    ∃ ε δ : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 < δ ∧ ∃ cutoff : ℕ, 3 ≤ cutoff ∧
      ∀ (m : ℕ), 1 ≤ m → ∀ lo hi : ℝ, lo ≤ hi →
      hi - lo ≤ Real.exp (H * m) → ∀ (Bidx Cidx : Type) (N : ℕ)
        (e : Fin (N + 1) ≃ Bidx ⊕ Cidx) (base : Fin (N + 1) → ℕ)
        (t : Bool → FrequencyTree ℤ (n + 2))
        (small : Bool → TreeLeafTuple (List Bidx) (n + 2))
        (pattern : Bool × MovingSampleIndex (n + 2) → Cidx)
        (p : Fin m → ℕ) [∀ i, Fact (p i).Prime],
      (∀ i, cutoff ≤ p i) →
      (∀ i b, ∀ s ∈ allFrequencyList (n + 2) (t b), s ≠ 0 ∧ s.natAbs < p i) →
      (∀ i b, ∀ j ∈ flattenMovingSlots (n + 2) (small b),
        (base (e.symm (.inl j)) : ZMod (p i)) ≠ 0) →
      (∀ i c, (base (e.symm (.inr c)) : ZMod (p i)) ≠ 0) →
      ∀ (twist : ∀ i, Bool → (ZMod (p i))ˣ)
        (perm : Equiv.Perm (TreeLeafIndex (n + 2) × Fin m)),
      4 * Fintype.card (arrangementGraph m perm).ConnectedComponent ≤
        3 * Fintype.card (TreeLeafIndex (n + 2)) →
      ∀ S : ∀ i, Finset (ZMod (p i)),
      (∀ i, (1 / 3 : ℝ) ≤ residueDensity (S i)) →
      (∀ i, residueDensity (S i) ≤ 2 / 3) →
      (∀ i, (S i).Nonempty) → (∀ i, (S i).card < p i) →
      ∀ β : Fin m → ℝ, (∀ i, 2 * β i ≤ ε) →
      (∀ i (χ : MulChar (ZMod (p i)) ℂ), χ ≠ 1 → ∀ a : ZMod (p i),
        ‖((S i).card : ℂ)⁻¹ * ∑ x ∈ S i, χ⁻¹ (-a - x)‖ ≤ β i) →
      ∀ amp : ℝ, 0 ≤ amp → amp ≤ Real.exp (F * m) →
      let W := (movingFourierVariationBudget ψ (Real.exp (A * m)) lo hi (n + 2) *
        (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ (n + 2) - 1)) ^ 2
      (∀ i, ‖(Fintype.card (TreeLeafIndex (n + 2) × Fin m → (ZMod (p i))ˣ) : ℂ)⁻¹ *
          ∑ z, frozenBulkSpectatorHaar base (n + 2) m t
            (fun b => movingPatternFiniteSmall e (n + 2) (small b))
            (movingPatternFiniteSamples e (n + 2) pattern) (twist i) perm
            (normalizedResidueTransform (S i)) z‖ ≤ δ) ∧
        (W * amp) * 4 ^ Fintype.card (TreeLeafIndex (n + 2) × Fin m) *
          δ ^ m ≤ Real.exp (-gain * m) := by
  obtain ⟨C, _, hkernel⟩ := exists_movingPatternKernelGain_window ψ (n + 2) r₀
    A H B D F gain hA hH
  obtain ⟨ε, hε, hε1, cutoff, hcutoff, hlocal⟩ := exists_frozenSpectatorGain n (C + F) gain
  let δ := signedBulkGainTarget (n + 2) (C + F) gain
  refine ⟨ε, δ, hε, hε1, signedBulkGainTarget_pos _ _ _, cutoff, hcutoff, ?_⟩
  intro m hm lo hi hhi hwidth Bidx Cidx N e base t small pattern p _ hp hfreq hsmall hsamples twist perm hgood
    S hlo hupper hS hSp β hβ hbias amp hamp hampBound
  dsimp only
  have hlocalBound (i : Fin m) :
      ‖(Fintype.card (TreeLeafIndex (n + 2) × Fin m → (ZMod (p i))ˣ) : ℂ)⁻¹ *
        ∑ z, frozenBulkSpectatorHaar base (n + 2) m t
          (fun b => movingPatternFiniteSmall e (n + 2) (small b))
          (movingPatternFiniteSamples e (n + 2) pattern) (twist i) perm
          (normalizedResidueTransform (S i)) z‖ ≤ δ :=
    hlocal (p i) (hp i) (Fin (N + 1)) base m (by omega) t _ _
      (fun b => movingGiantFrequencyUnits_of_bounds (t b) (hfreq i b))
      (fun b => movingPatternFiniteSmall_unit e base (small b) (hsmall i b))
      (movingPatternFiniteSamples_units e base pattern (hsamples i))
      (twist i) perm hgood (S i) (hlo i) (hupper i) (hS i) (hSp i) (β i) (hβ i) (hbias i)
  exact ⟨hlocalBound, hkernel m hm lo hi hhi hwidth amp δ hamp hampBound
    (signedBulkGainTarget_pos _ _ _).le le_rfl⟩

end Ostmann

end OAI
