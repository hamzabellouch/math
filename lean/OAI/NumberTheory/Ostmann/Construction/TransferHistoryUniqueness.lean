import OAI.NumberTheory.Ostmann.Construction.TransferFrequencyRigidity
import OAI.NumberTheory.Ostmann.Arithmetic.FrequencyTreeSum

namespace OAI

/-! # A fixed top assignment and root frequency determine the full valid history -/

namespace Ostmann

/-- A state records the current actual labels. Child states insert the
reconstructed pivot and retain the corresponding branch. -/
structure TransferHistorySystem (State : Type*) where
  leftProduct : State → ℕ
  rightProduct : State → ℕ
  childBound : State → ℕ
  pivotBound : State → ℕ
  leftState : State → ℕ → State
  rightState : State → ℕ → State

/-- The conditions used by the rigidity argument are all original support
conditions or the strict product-range inequality. -/
structure ValidTransferNode {State : Type*} (sys : TransferHistorySystem State)
    (σ : State) (s v w : ℤ) (P : ℕ) : Prop where
  root_ne_zero : s ≠ 0
  root_unit : IsCoprime s (sys.rightProduct σ : ℤ)
  relation : v * sys.rightProduct σ - w * sys.leftProduct σ = s * P
  pivot_pos : 0 < P
  pivot_bound : P ≤ sys.pivotBound σ
  left_bound : v.natAbs ≤ sys.childBound σ
  right_bound : w.natAbs ≤ sys.childBound σ
  range_gap : 2 * sys.pivotBound σ * sys.childBound σ < sys.rightProduct σ
  pivot_unit : P.Coprime w.natAbs

def ValidTransferHistory {State : Type*} (sys : TransferHistorySystem State) :
    (n : ℕ) → State → FrequencyTree ℤ n → Prop
  | 0, _, _ => True
  | n + 1, σ, x => ∃ P : ℕ,
      ValidTransferNode sys σ x.1 (frequencyRoot n x.2.1) (frequencyRoot n x.2.2) P ∧
      ValidTransferHistory sys n (sys.leftState σ P) x.2.1 ∧
      ValidTransferHistory sys n (sys.rightState σ P) x.2.2

/-- Inserted ancestor pivots are part of the state. Fixing their value at a
node therefore fixes both child states before the induction is applied. -/
theorem validTransferHistory_unique {State : Type*} (sys : TransferHistorySystem State)
    (n : ℕ) (σ : State) (x y : FrequencyTree ℤ n)
    (hx : ValidTransferHistory sys n σ x) (hy : ValidTransferHistory sys n σ y)
    (hroot : frequencyRoot n x = frequencyRoot n y) : x = y := by
  induction n generalizing σ with
  | zero => exact hroot
  | succ n ih =>
    obtain ⟨P, hP, hxL, hxR⟩ := hx
    obtain ⟨Q, hQ, hyL, hyR⟩ := hy
    have hr : x.1 = y.1 := hroot
    have hrelQ : frequencyRoot n y.2.1 * sys.rightProduct σ -
        frequencyRoot n y.2.2 * sys.leftProduct σ = x.1 * Q := by
      rw [hr]
      exact hQ.relation
    obtain ⟨hv, hw, hPQ⟩ := transfer_substitution_unique
      (sys.leftProduct σ) (sys.rightProduct σ) P Q (sys.childBound σ) (sys.pivotBound σ)
      x.1 (frequencyRoot n x.2.1) (frequencyRoot n x.2.2)
      (frequencyRoot n y.2.1) (frequencyRoot n y.2.2)
      hP.root_ne_zero hP.root_unit hP.relation hrelQ hP.pivot_pos hP.pivot_bound hQ.pivot_bound
      hP.right_bound hQ.right_bound hP.range_gap hP.pivot_unit hQ.pivot_unit
    subst Q
    have heL := ih (sys.leftState σ P) x.2.1 y.2.1 hxL hyL hv
    have heR := ih (sys.rightState σ P) x.2.2 y.2.2 hxR hyR hw
    exact Prod.ext hr (Prod.ext heL heR)

theorem validTransferHistory_root_injective {State : Type*}
    (sys : TransferHistorySystem State) (n : ℕ) (σ : State) :
    Set.InjOn (frequencyRoot n) {x | ValidTransferHistory sys n σ x} := by
  intro x hx y hy hroot
  exact validTransferHistory_unique sys n σ x y hx hy hroot

end Ostmann

end OAI
