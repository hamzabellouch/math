import OAI.NumberTheory.Ostmann.Arithmetic.FrequencyModelValidity
import OAI.NumberTheory.Ostmann.Arithmetic.MovingAdaptiveSupport

namespace OAI

/-! # Constructed split support for the arithmetic frequency gate -/

namespace Ostmann
open scoped Classical

noncomputable def frequencyModelHistory {σ : Type*} (value : σ → ℕ)
    (R : ℕ) (n : ℕ) (t : FrequencyTree ℤ n)
    (small bulk : TreeLeafTuple (List σ) n) (a : MovingSampleSlots σ n) (x y : ℤ)
    (z : TreeLeafTuple (ZMod (R ^ (n - 1 + 2)))ˣ n)
    (hz : treeIntegerResidues (R ^ (n - 1 + 2)) n
      (treeLeafMap (fun q : ℕ => (q : ℤ)) n (movingSlotValues value n bulk)) z) :
    SampledPivotHistory n (R ^ (n - 1 + 2)) where
  bulk := treeLeafMap (fun q : ℕ => (q : ℤ)) n (movingSlotValues value n bulk)
  residue := z
  pivots := frequencyModelPivots value R n (buildMovingSlotData n t small bulk a) x y
  compatible := hz

theorem frequencyModelHistory_valid {σ : Type*} (value : σ → ℕ)
    (R : ℕ) (S : Finset ℤ) (n : ℕ) (t : FrequencyTree S n)
    (small bulk : TreeLeafTuple (List σ) n) (a : MovingSampleSlots σ n) (x y : ℤ)
    (hsmall : ∀ i, IsCoprime (value i : ℤ) (R : ℤ)) (hR : ∀ j : Fin (2 ^ n - 1), (singleTreeNodeFrequencies S n t j.val).root.natAbs ∣ R)
    (z : TreeLeafTuple (ZMod (R ^ (n - 1 + 2)))ˣ n)
    (hz : treeIntegerResidues (R ^ (n - 1 + 2)) n
      (treeLeafMap (fun q : ℕ => (q : ℤ)) n (movingSlotValues value n bulk)) z)
    (hg : movingFrequencyGate value R
      (buildMovingSlotData n (frequencyTreeMap Subtype.val n t) small bulk a) x y) :
    (frequencyModelHistory value R n (frequencyTreeMap Subtype.val n t) small bulk a x y z hz).modularValid
      (frequencyModelAncestorScheme value S n t small a x y) R (n - 1)
      (movingSampleCompensation value n small a) := by
  constructor
  · exact frequencyModel_modularEquations value R S n t small bulk a x y hsmall hg
  · intro j
    exact frequencyModel_coefficient_units value R S n t small bulk a x y hsmall hR hg j

noncomputable def frequencyModelAdaptiveData {σ : Type*} (value : σ → ℕ)
    (S : Finset ℤ) (n R : ℕ) (t : FrequencyTree S n)
    (hS : ∀ s ∈ S, s ≠ 0) (hR : ∀ j : Fin (2 ^ n - 1), (singleTreeNodeFrequencies S n t j.val).root.natAbs ∣ R)
    (small : TreeLeafTuple (List σ) n) (a : MovingSampleSlots σ n) (x y : ℤ) :
    (ZMod (R ^ (n - 1 + 2)))ˣ → List (ZMod (R ^ (n - 1 + 2)))ˣ →
      Option (ArithmeticSplitData (R ^ (n - 1 + 2))) :=
  modularAdaptiveData n R (n - 1)
    (frequencyModelAncestorScheme value S n t small a x y)
    (movingSampleCompensation value n small a)
    (fun i => hS _ (singleTreeNodeFrequencies_root_mem S n t i.val i.isLt))
    hR

theorem frequencyModelAdaptiveData_frequencies {σ : Type*} (value : σ → ℕ)
    (S : Finset ℤ) (n R : ℕ) (t : FrequencyTree S n)
    (hS : ∀ s ∈ S, s ≠ 0) (hR : ∀ j : Fin (2 ^ n - 1), (singleTreeNodeFrequencies S n t j.val).root.natAbs ∣ R)
    (small : TreeLeafTuple (List σ) n) (a : MovingSampleSlots σ n) (x y : ℤ)
    (total : (ZMod (R ^ (n - 1 + 2)))ˣ) (past : List (ZMod (R ^ (n - 1 + 2)))ˣ)
    (d : ArithmeticSplitData (R ^ (n - 1 + 2)))
    (hd : frequencyModelAdaptiveData value S n R t hS hR small a x y total past = some d) :
    d.hasFrequencies (singleTreeNodeFrequencies S n t past.length) := by
  by_cases hj : past.length < 2 ^ n - 1
  · exact modularAdaptiveData_frequencies n R (n - 1)
      (frequencyModelAncestorScheme value S n t small a x y)
      (movingSampleCompensation value n small a) _ _ total past hj d hd
  · simp only [frequencyModelAdaptiveData, modularAdaptiveData, hj, dite_false] at hd
    cases hd

/-- Every residue tuple accepted by the existing frequency gate lies in the
constructed sequential support. No prime-line or integer-integrality test
has been reintroduced. -/
theorem frequencyModelAdaptiveData_support {σ : Type*} (value : σ → ℕ)
    (S : Finset ℤ) (n R : ℕ) [NeZero (R ^ (n - 1 + 2))] (t : FrequencyTree S n)
    (hS : ∀ s ∈ S, s ≠ 0) (hR : ∀ j : Fin (2 ^ n - 1), (singleTreeNodeFrequencies S n t j.val).root.natAbs ∣ R)
    (small bulk : TreeLeafTuple (List σ) n) (a : MovingSampleSlots σ n) (x y : ℤ)
    (hsmall : ∀ i, IsCoprime (value i : ℤ) (R : ℤ))
    (z : TreeLeafTuple (ZMod (R ^ (n - 1 + 2)))ˣ n)
    (hz : treeIntegerResidues (R ^ (n - 1 + 2)) n
      (treeLeafMap (fun q : ℕ => (q : ℤ)) n (movingSlotValues value n bulk)) z)
    (hg : movingFrequencyGate value R
      (buildMovingSlotData n (frequencyTreeMap Subtype.val n t) small bulk a) x y) :
    singleArithmeticLeafSupport n
      (frequencyModelAdaptiveData value S n R t hS hR small a x y) z = 1 := by
  apply modularAdaptiveData_actual_support n R (n - 1)
    (frequencyModelAncestorScheme value S n t small a x y)
    (movingSampleCompensation value n small a)
    (fun i => movingFrameConstants_compensation_coprime value R hsmall n small a
      (preorderNodePath n i))
    (fun i => Nat.le_pred_of_lt (preorderNodePath_length n i))
    (fun i => hS _ (singleTreeNodeFrequencies_root_mem S n t i.val i.isLt))
    hR
    (frequencyModelHistory value R n (frequencyTreeMap Subtype.val n t) small bulk a x y z hz)
  exact frequencyModelHistory_valid value R S n t small bulk a x y hsmall hR z hz hg

end Ostmann

end OAI
