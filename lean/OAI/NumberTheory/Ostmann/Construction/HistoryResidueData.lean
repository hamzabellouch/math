import OAI.NumberTheory.Ostmann.Arithmetic.SingleFrequencyModulus
import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticResidueSplit
import OAI.NumberTheory.Ostmann.Arithmetic.SingleHistorySupport

namespace OAI

/-! # Adaptive residue data on the exact frequency-history modulus -/

namespace Ostmann

open scoped Classical

/-- The root frequency and its divisibility are supplied by the actual
history, rather than by a hypothesis on an arbitrary arithmetic record. -/
def historyResidueSplit (S : Finset ℤ) (hS : ∀ s ∈ S, s ≠ 0)
    (n k : ℕ) (t : FrequencyTree S n) (j : ℕ) (hj : j < 2 ^ n - 1)
    (A B : ZMod (historyFrequencyModulus S n k t))
    (P : (ZMod (historyFrequencyModulus S n k t))ˣ) :
    ArithmeticResidueSplit (historyFrequencyModulus S n k t) where
  frequencies := singleTreeNodeFrequencies S n t j
  frequency_ne_zero := hS _ (singleTreeNodeFrequencies_root_mem S n t j hj)
  frequency_dvd := by
    apply history_node_dvd_frequencyModulus S n k t
    have hj' : j < (singleFrequencySplitList S n t).length := by
      simpa only [singleFrequencySplitList_length] using hj
    rw [singleTreeNodeFrequencies, List.getD_eq_getElem _ _ hj']
    exact List.getElem_mem hj'
  leftFactor := A
  rightFactor := B
  parentProduct := P

/-- Coefficients may use the total product and the exposed split prefix.
They cannot inspect a future split coordinate. Invalid unit coefficients
are rejected by the exact `toData` test. -/
noncomputable def historyResidueData (S : Finset ℤ) (hS : ∀ s ∈ S, s ≠ 0)
    (n k : ℕ) (t : FrequencyTree S n)
    (A B : (ZMod (historyFrequencyModulus S n k t))ˣ →
      List (ZMod (historyFrequencyModulus S n k t))ˣ → ZMod (historyFrequencyModulus S n k t))
    (P : (ZMod (historyFrequencyModulus S n k t))ˣ →
      List (ZMod (historyFrequencyModulus S n k t))ˣ → (ZMod (historyFrequencyModulus S n k t))ˣ)
    (total : (ZMod (historyFrequencyModulus S n k t))ˣ)
    (past : List (ZMod (historyFrequencyModulus S n k t))ˣ) :
    Option (ArithmeticSplitData (historyFrequencyModulus S n k t)) :=
  if hj : past.length < 2 ^ n - 1 then
    (historyResidueSplit S hS n k t past.length hj (A total past) (B total past) (P total past)).toData
  else none

theorem historyResidueData_frequencies (S : Finset ℤ) (hS : ∀ s ∈ S, s ≠ 0)
    (n k : ℕ) (t : FrequencyTree S n)
    (A B : (ZMod (historyFrequencyModulus S n k t))ˣ →
      List (ZMod (historyFrequencyModulus S n k t))ˣ → ZMod (historyFrequencyModulus S n k t))
    (P : (ZMod (historyFrequencyModulus S n k t))ˣ →
      List (ZMod (historyFrequencyModulus S n k t))ˣ → (ZMod (historyFrequencyModulus S n k t))ˣ)
    (total : (ZMod (historyFrequencyModulus S n k t))ˣ)
    (past : List (ZMod (historyFrequencyModulus S n k t))ˣ)
    (d : ArithmeticSplitData (historyFrequencyModulus S n k t))
    (hd : historyResidueData S hS n k t A B P total past = some d) :
    d.hasFrequencies (singleTreeNodeFrequencies S n t past.length) := by
  unfold historyResidueData at hd
  split_ifs at hd with hj
  · exact ArithmeticResidueSplit.toData_frequencies _ _ hd

theorem historyResidueData_test (S : Finset ℤ) (hS : ∀ s ∈ S, s ≠ 0)
    (n k : ℕ) (t : FrequencyTree S n)
    (A B : (ZMod (historyFrequencyModulus S n k t))ˣ →
      List (ZMod (historyFrequencyModulus S n k t))ˣ → ZMod (historyFrequencyModulus S n k t))
    (P : (ZMod (historyFrequencyModulus S n k t))ˣ →
      List (ZMod (historyFrequencyModulus S n k t))ˣ → (ZMod (historyFrequencyModulus S n k t))ˣ)
    (total : (ZMod (historyFrequencyModulus S n k t))ˣ)
    (past : List (ZMod (historyFrequencyModulus S n k t))ˣ)
    (x : (ZMod (historyFrequencyModulus S n k t))ˣ)
    (hj : past.length < 2 ^ n - 1) :
    singleArithmeticSplitTest (historyResidueData S hS n k t A B P total past) x ↔
      (historyResidueSplit S hS n k t past.length hj (A total past) (B total past) (P total past)).support x := by
  rw [historyResidueData, dite_eq_left hj]
  rw [← ArithmeticResidueSplit.toData_test]
  cases hd : (historyResidueSplit S hS n k t past.length hj
    (A total past) (B total past) (P total past)).toData <;>
    simp [singleArithmeticSplitTest]

end Ostmann

end OAI
