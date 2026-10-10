import OAI.NumberTheory.Ostmann.Construction.ConstituentSupportedFamilyEnergy
import OAI.NumberTheory.Ostmann.Construction.FullAtomProductBounds
import OAI.NumberTheory.Ostmann.Construction.SelectedAnchorHarmonicBudget

namespace OAI

/-! # The actual code-preserving contribution after summing the external pivot -/

namespace Ostmann
open scoped Classical BigOperators

theorem selected_anchor_diagonal_on_product {I D R : Type*}
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
    (bulk : Fin m ↪ (Σ a, Fin (size a)))
    (hrole : ∀ i, role (bulk i).1 = .word)
    (lo hi : I → ℕ) (hranges : ranges = atomIntervalRanges role lo hi)
    (a b : ℕ) (ha : 0 < a) (gap E L z : ℝ)
    (hlower : 0 < ∏ h : CopyScheduleH role n, (lo (copyScheduleOrigin n h.val) : ℝ))
    (hgap : Real.exp gap * (b : ℝ) ≤ ∏ h : CopyScheduleH role n, (lo (copyScheduleOrigin n h.val) : ℝ))
    (hL : 0 < L) (hz : 0 < z) (hm : (m : ℝ) ≤ z * L)
    (hmass : ∀ h : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n,
      0 < ∑ p ∈ Q (copyScheduleOrigin n h.val), (p : ℝ)⁻¹)
    (hbulk : ∀ x, L ≤ ∑ p ∈ Q (copyScheduleOrigin n
      (selectedBulkCoordinates (fun i : Σ a, Fin (size a) => role i.1) n m bulk hrole x).val.val),
        (p : ℝ)⁻¹)
    (henergy : ∀ M ∈ Finset.Icc a b,
      constituentHistoryEnergy role size n P Q childBound pivotBound ranges leaf hist M ≤
        Real.exp E) :
    (∑ M ∈ Finset.Icc a b,
      (constituentMatchingFamily role size χ κ pivot n P hP Q childBound pivotBound ranges
        leaf hist (selectedAnchorMatchingSet
          (fun i : Σ a, Fin (size a) => role i.1) n m bulk hrole) M).re) ≤
      Real.exp (-gap) *
        (Fintype.card (SelectedNonbulkH (fun i : Σ a, Fin (size a) => role i.1) n m bulk hrole)).factorial *
        (∏ h : SelectedNonbulkH (fun i : Σ a, Fin (size a) => role i.1) n m bulk hrole,
          (∑ p ∈ Q (copyScheduleOrigin n h.val.val), (p : ℝ)⁻¹)⁻¹) *
        Real.exp ((Real.log 2 + Real.log z) * (2 ^ n * m : ℕ) + E) := by
  have h₁ := constituentMatchingFamily_interval_on_product role size χ κ pivot n P hP Q
    childBound pivotBound ranges leaf hist hκ hhist root hroot
    (selectedAnchorMatchingSet (fun i : Σ a, Fin (size a) => role i.1) n m bulk hrole)
    a b ha gap (Real.exp E) (∏ h : CopyScheduleH role n, (lo (copyScheduleOrigin n h.val) : ℝ))
    (Real.exp_pos _).le hlower hgap (by
      intro M _ u l d hw
      subst ranges
      have hb := (fullAtomTransferWeight_inserted_H_product_bounds role size n
        childBound pivotBound lo hi leaf (hist d) (fun h => (l h : ℕ))
        (fun y => (u y : ℕ)) M hw).1
      exact_mod_cast hb) henergy
  have h₂ := selected_anchor_harmonic_bound
    (fun i : Σ a, Fin (size a) => role i.1) n m bulk hrole
    (fun h => ∑ p ∈ Q (copyScheduleOrigin n h.val), (p : ℝ)⁻¹)
    L z hL hz hm hmass hbulk
  calc
    _ ≤ _ := h₁
    _ = Real.exp (-gap) *
        (((selectedAnchorMatchingSet
          (fun i : Σ a, Fin (size a) => role i.1) n m bulk hrole).card : ℝ) *
          (∏ h : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n,
            (∑ p ∈ Q (copyScheduleOrigin n h.val), (p : ℝ)⁻¹)⁻¹) *
          Real.exp E) := by ring
    _ ≤ Real.exp (-gap) *
        (((Fintype.card (SelectedNonbulkH (fun i : Σ a, Fin (size a) => role i.1) n m bulk hrole)).factorial *
          (∏ h : SelectedNonbulkH (fun i : Σ a, Fin (size a) => role i.1) n m bulk hrole,
            (∑ p ∈ Q (copyScheduleOrigin n h.val.val), (p : ℝ)⁻¹)⁻¹) *
          Real.exp ((Real.log 2 + Real.log z) * (2 ^ n * m : ℕ))) *
          Real.exp E) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right h₂ (Real.exp_pos _).le) (Real.exp_pos _).le
    _ = _ := by rw [Real.exp_add]; ring

end Ostmann

end OAI
