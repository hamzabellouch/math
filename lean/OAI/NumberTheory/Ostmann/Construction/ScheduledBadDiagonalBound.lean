import OAI.NumberTheory.Ostmann.Construction.ConstituentFamilyEnergy
import OAI.NumberTheory.Ostmann.Construction.BadDiagonalNormalization

namespace OAI

/-! # The actual bad-matching contribution after summing the external pivot -/

namespace Ostmann
open scoped Classical BigOperators

theorem scheduled_bad_diagonal_bound {I D R : Type*}
    [Fintype I] [Fintype D] [Fintype R]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
    (n m : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
    (hκ : ∀ i p, ‖κ i p‖ ≤ 1) (hhist : Function.Injective hist) (root : D → R)
    (hroot : ∀ d d', root d = root d' ↔ frequencyRoot n (hist d) = frequencyRoot n (hist d'))
    (word : Fin m ≃ {i : Σ a, Fin (size a) // role i.1 = .word}) (hm0 : 0 < m)
    (lo : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → ℝ)
    (hlo : ∀ h, 0 < lo h)
    (hcell : ∀ h p, p ∈ Q (copyScheduleOrigin n h.val) → lo h ≤ (p : ℝ))
    (a b : ℕ) (ha : 0 < a) (gap E L z : ℝ)
    (hgap : Real.exp gap * (b : ℝ) ≤ ∏ h, lo h)
    (hL : 0 < L) (hz : 0 < z) (hm : (m : ℝ) ≤ z * L)
    (hmass : ∀ h : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n,
      0 < ∑ p ∈ Q (copyScheduleOrigin n h.val), (p : ℝ)⁻¹)
    (hbulk : ∀ x, L ≤ ∑ p ∈ Q (copyScheduleOrigin n
      (scheduledBulkCoordinates (fun i : Σ a, Fin (size a) => role i.1) n m word x).val.val),
        (p : ℝ)⁻¹)
    (henergy : ∀ M ∈ Finset.Icc a b,
      constituentHistoryEnergy role size n P Q childBound pivotBound ranges leaf hist M ≤
        Real.exp E) :
    (∑ M ∈ Finset.Icc a b,
      (constituentMatchingFamily role size χ κ pivot n P hP Q childBound pivotBound ranges
        leaf hist (scheduledDiagonalBadMatchingSet
          (fun i : Σ a, Fin (size a) => role i.1) n m word) M).re) ≤
      Real.exp (-gap) *
        (((2 ^ n + 1) * (2 ^ n) ^ (2 * 2 ^ n) : ℕ) : ℝ) *
        (Fintype.card (ScheduledNonbulkH (fun i : Σ a, Fin (size a) => role i.1) n)).factorial *
        (∏ h : ScheduledNonbulkH (fun i : Σ a, Fin (size a) => role i.1) n,
          (∑ p ∈ Q (copyScheduleOrigin n h.val.val), (p : ℝ)⁻¹)⁻¹) *
        Real.exp ((Real.log z + Real.log (2 ^ n : ℕ) / 4 + 2) * (2 ^ n * m : ℕ) + E) := by
  have h₁ := constituentMatchingFamily_interval_le role size χ κ pivot n P hP Q
    childBound pivotBound ranges leaf hist hκ hhist root hroot
    (scheduledDiagonalBadMatchingSet (fun i : Σ a, Fin (size a) => role i.1) n m word)
    lo hlo hcell a b ha gap (Real.exp E) (Real.exp_pos _).le hgap henergy
  have h₂ := scheduled_diagonal_bad_harmonic_bound
    (fun i : Σ a, Fin (size a) => role i.1) n m word hm0
    (fun h => ∑ p ∈ Q (copyScheduleOrigin n h.val), (p : ℝ)⁻¹)
    L z 0 hL hz hm hmass hbulk
  simp only [zero_mul, Real.exp_zero, mul_one, add_zero] at h₂
  calc
    _ ≤ _ := h₁
    _ = Real.exp (-gap) *
        (((scheduledDiagonalBadMatchingSet
          (fun i : Σ a, Fin (size a) => role i.1) n m word).card : ℝ) *
          (∏ h : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n,
            (∑ p ∈ Q (copyScheduleOrigin n h.val), (p : ℝ)⁻¹)⁻¹) *
          Real.exp E) := by ring
    _ ≤ Real.exp (-gap) *
        (((((2 ^ n + 1) * (2 ^ n) ^ (2 * 2 ^ n) : ℕ) : ℝ) *
          (Fintype.card (ScheduledNonbulkH (fun i : Σ a, Fin (size a) => role i.1) n)).factorial *
          (∏ h : ScheduledNonbulkH (fun i : Σ a, Fin (size a) => role i.1) n,
            (∑ p ∈ Q (copyScheduleOrigin n h.val.val), (p : ℝ)⁻¹)⁻¹) *
          Real.exp ((Real.log z + Real.log (2 ^ n : ℕ) / 4 + 2) * (2 ^ n * m : ℕ))) *
          Real.exp E) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right h₂ (Real.exp_pos _).le) (Real.exp_pos _).le
    _ = _ := by rw [Real.exp_add]; ring

end Ostmann

end OAI
