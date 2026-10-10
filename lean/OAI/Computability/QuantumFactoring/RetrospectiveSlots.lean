import Mathlib
import OAI.Computability.QuantumFactoring.RetrospectiveLists

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open AuxiliaryTree OrderTrial

/-- The usable-slot test is just range plus Euclidean gcd, not an order oracle. -/
def residueUsable (a m : ℕ) : Prop := a < m ∧ a.Coprime m
lemma residueUsable_iff {n : ℕ} (a m : Basis n) :
    residueUsable (bitsValue a).toNat (bitsValue m).toNat ↔ OrderSlots.Usable a m := by
  simp only [residueUsable,OrderSlots.Usable,ZMod.isUnit_iff_coprime]

/-- Test the same completed order slot using the later supplied node record.
Unusable list entries (including out-of-range words) use the source dummy test. -/
noncomputable def dataOrderPassed {n : ℕ} (data : FactorData) (a m : Basis n)
    (r : OrderSlots.Result n) : Prop := by
  classical
  exact
  if residueUsable (bitsValue a).toNat (bitsValue m).toNat then
    Completion.test
      (fun x => orderResult (OrderSlots.sampleExponent n) n a m (n^5) x=
        dataOrder data (bitsValue a).toNat (bitsValue m).toNat)
      (fun y => y=natBasis _ (dataOrder data (bitsValue a).toNat (bitsValue m).toNat))
      (dataOrderSuccess data (bitsValue a).toNat (bitsValue m).toNat (n^5)) (Completion.target n) r
  else Completion.test (fun _=>True) (fun y=>y=natBasis _ 0) 1 (Completion.target n) r

lemma dataOrderPassed_correct {M n : ℕ} (hM : 0<M) (a m : Basis n)
    (hm : 2 ≤ (bitsValue m).toNat) (hd : (bitsValue m).toNat∣M)
    (r : OrderSlots.Result n) :
    dataOrderPassed (trueData M) a m r ↔ OrderSlots.passed a m r := by
  classical
  rw [dataOrderPassed,residueUsable_iff]
  by_cases h : OrderSlots.Usable a m
  · rw [ite_eq_left h,OrderSlots.passed,dite_eq_left h,
      dataOrder_correct hM hm hd h.2.unit h.2.unit_spec.symm,
      dataOrderSuccess_correct hM hm hd h.2.unit h.2.unit_spec.symm]
    change Completion.test _ _ _ _ r ↔ Completion.passed _ (natBasis _ (OrderSlots.unitOrder a m)) _ _ r
    rw [OrderSlots.unitOrder,dite_eq_left h]
    exact Completion.test_eq_passed _ _ _ _ _ (fun _=>Iff.rfl) r
  · rw [ite_eq_right h,OrderSlots.passed,dite_eq_right h]
    change Completion.test _ _ _ _ r ↔ Completion.passed _ (natBasis _ (OrderSlots.unitOrder a m)) _ _ r
    rw [OrderSlots.unitOrder,dite_eq_right h]
    exact Completion.test_eq_passed _ _ _ _ _ (fun _=>Iff.rfl) r

noncomputable def dataSplitPassed {n : ℕ} (data : FactorData) (m : Basis n) (hn : 0<n)
    (r : UniversalSplit.Raw n) : Prop := by
  classical
  exact
  if UniversalSplit.Hard (bitsValue m).toNat then
    dataListPassed data m hn r.1 ∧ ∀ i,dataOrderPassed data (FixedSplit.bases r.1 i) m (r.2 i)
  else UniversalSplit.dummy r

/-- All list/order/retention decisions are on the actual retained raw block.
The record may be that of any actual node whose label is divisible by m. -/
lemma dataSplitPassed_correct {M n : ℕ} (hM : 0<M) (m : Basis n)
    (hm : 2 ≤ (bitsValue m).toNat) (hd : (bitsValue m).toNat∣M) (hn : 0<n)
    (r : UniversalSplit.Raw n) :
    dataSplitPassed (trueData M) m hn r ↔ UniversalSplit.passed m r := by
  classical
  rw [dataSplitPassed,UniversalSplit.passed]
  split_ifs with hh
  · change (_ ∧ ∀ i,_) ↔ (_ ∧ ∀ i,_)
    exact and_congr (dataListPassed_correct hM m hm hd hn r.1)
      (forall_congr' (fun i=>dataOrderPassed_correct hM _ m hm hd (r.2 i)))
  · rfl

end ExactQuantumFactoring


end

end OAI
