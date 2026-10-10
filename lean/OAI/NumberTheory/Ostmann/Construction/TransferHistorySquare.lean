import Mathlib.Analysis.Complex.Basic
import OAI.NumberTheory.Ostmann.Construction.TransferHistoryUniqueness

namespace OAI

/-! # No history multiplicity is lost when the root-frequency square is formed -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def historiesAtRoot {State : Type*} (sys : TransferHistorySystem State)
    (n : ℕ) (σ : State) (T : Finset (FrequencyTree ℤ n)) (s : ℤ) :
    Finset (FrequencyTree ℤ n) :=
  T.filter fun x => ValidTransferHistory sys n σ x ∧ frequencyRoot n x = s

theorem historiesAtRoot_card_le_one {State : Type*} (sys : TransferHistorySystem State)
    (n : ℕ) (σ : State) (T : Finset (FrequencyTree ℤ n)) (s : ℤ) :
    (historiesAtRoot sys n σ T s).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  have hx' := (Finset.mem_filter.mp hx).2
  have hy' := (Finset.mem_filter.mp hy).2
  exact validTransferHistory_unique sys n σ x y hx'.1 hy'.1 (hx'.2.trans hy'.2.symm)

/-- The exact square identity uses uniqueness before any averaging or
coefficient majorization. It applies equally to a fixed external pivot state. -/
theorem history_root_square_eq {State : Type*} (sys : TransferHistorySystem State)
    (n : ℕ) (σ : State) (T : Finset (FrequencyTree ℤ n)) (s : ℤ)
    (c : FrequencyTree ℤ n → ℂ) :
    ‖∑ x ∈ historiesAtRoot sys n σ T s, c x‖ ^ 2 =
      ∑ x ∈ historiesAtRoot sys n σ T s, ‖c x‖ ^ 2 := by
  let F := historiesAtRoot sys n σ T s
  change ‖∑ x ∈ F, c x‖ ^ 2 = ∑ x ∈ F, ‖c x‖ ^ 2
  have hcard : F.card ≤ 1 := historiesAtRoot_card_le_one sys n σ T s
  obtain hF | ⟨x, hx⟩ := F.eq_empty_or_nonempty
  · rw [hF]
    simp
  · have hFx : F = {x} := by
      ext y
      constructor
      · intro hy
        exact Finset.mem_singleton.mpr (Finset.card_le_one.mp hcard y hy x hx)
      · intro hy
        simpa only [Finset.mem_singleton.mp hy] using hx
    rw [hFx]
    simp

end Ostmann

end OAI
