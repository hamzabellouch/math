import Mathlib
import OAI.Computability.QuantumFactoring.PhysicalDataLog
import OAI.Computability.QuantumFactoring.RetrospectiveSlots
import OAI.Computability.QuantumFactoring.HardFilterCircuit
import OAI.Computability.QuantumFactoring.RetainedListFilter
import OAI.Computability.QuantumFactoring.RetainedListDummy
import OAI.Computability.QuantumFactoring.RetainedOrderTest

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic OrderTrial
namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

def splitModulus (t : ℕ) (raw : BooleanNetwork (M.width t) (FixedSplit.width n)) :=
  raw.comp (FixedSplit.modulusNet n)
def splitList (t : ℕ) (raw : BooleanNetwork (M.width t) (FixedSplit.width n)) :=
  (raw.comp (FixedSplit.launchWires n)).comp (FixedSplit.listWires n)
def splitBase (t : ℕ) (raw : BooleanNetwork (M.width t) (FixedSplit.width n)) (i : Fin (n^5)) :=
  raw.comp (FixedSplit.actualBaseNet i)
def splitOrder (t : ℕ) (raw : BooleanNetwork (M.width t) (FixedSplit.width n)) (i : Fin (n^5)) :=
  raw.comp (FixedSplit.actualOrderRawNet i)

def splitActualFilter (hn : 0<n) (t : ℕ) (raw : BooleanNetwork (M.width t) (FixedSplit.width n)) :
    BooleanNetwork (M.width t) 1 :=
  (M.retainedListFilter hn t (M.splitModulus t raw) (M.splitList t raw)).band
    (all (List.ofFn (fun i : Fin (n^5)=>M.retainedOrderFilter t (M.splitBase t raw i)
      (M.splitModulus t raw) (M.splitOrder t raw i))))

def splitDummyFilter (t : ℕ) (raw : BooleanNetwork (M.width t) (FixedSplit.width n)) :
    BooleanNetwork (M.width t) 1 :=
  (M.listDummyFilter t (M.splitModulus t raw) (M.splitList t raw)).band
    (all (List.ofFn (fun i : Fin (n^5)=>M.orderDummyFilter t (M.splitBase t raw i)
      (M.splitModulus t raw) (M.splitOrder t raw i))))

def retainedSplitFilter (hn : 0<n) (t : ℕ) (raw : BooleanNetwork (M.width t) (FixedSplit.width n)) :
    BooleanNetwork (M.width t) 1 :=
  ((UniversalSplit.hardOn (M.splitModulus t raw)).band (M.splitActualFilter hn t raw)).bor
    ((UniversalSplit.hardOn (M.splitModulus t raw)).bnot.band (M.splitDummyFilter t raw))

lemma splitModulus_eval (t : ℕ) (raw : BooleanNetwork (M.width t) (FixedSplit.width n))
    (x : Basis (M.width t)) (q : Basis n) (r : UniversalSplit.Raw n)
    (hr : raw.eval x=FixedSplit.encoding q r) :
    (M.splitModulus t raw).eval x=q := by
  rw [splitModulus,eval_comp,hr,FixedSplit.modulusNet_eval]
lemma splitList_eval (t : ℕ) (raw : BooleanNetwork (M.width t) (FixedSplit.width n))
    (x : Basis (M.width t)) (q : Basis n) (r : UniversalSplit.Raw n)
    (hr : raw.eval x=FixedSplit.encoding q r) :
    (M.splitList t raw).eval x=PhysicalListSlots.layout n r.1 := by
  rw [splitList,eval_comp,eval_comp,hr,FixedSplit.launchWires_eval,FixedSplit.listWires_eval]
lemma splitBase_eval (t : ℕ) (raw : BooleanNetwork (M.width t) (FixedSplit.width n))
    (x : Basis (M.width t)) (q : Basis n) (r : UniversalSplit.Raw n)
    (hr : raw.eval x=FixedSplit.encoding q r) (i : Fin (n^5)) :
    (M.splitBase t raw i).eval x=FixedSplit.bases r.1 i := by
  rw [splitBase,eval_comp,hr,FixedSplit.actualBaseNet_eval]
lemma splitOrder_eval (t : ℕ) (raw : BooleanNetwork (M.width t) (FixedSplit.width n))
    (x : Basis (M.width t)) (q : Basis n) (r : UniversalSplit.Raw n)
    (hr : raw.eval x=FixedSplit.encoding q r) (i : Fin (n^5)) :
    (M.splitOrder t raw i).eval x=OrderSlots.layout n (r.2 i) := by
  rw [splitOrder,eval_comp,hr,FixedSplit.actualOrderRawNet_eval]

lemma splitDummyFilter_exact (t : ℕ) (raw : BooleanNetwork (M.width t) (FixedSplit.width n))
    (x : Basis (M.width t)) (q : Basis n) (r : UniversalSplit.Raw n)
    (hr : raw.eval x=FixedSplit.encoding q r) :
    (M.splitDummyFilter t raw).eval x 0=true ↔ UniversalSplit.dummy r := by
  rw [splitDummyFilter,eval_band,Bool.and_eq_true,
    M.listDummyFilter_exact t _ _ x r.1 (M.splitList_eval t raw x q r hr),all_eval]
  simp only [List.mem_ofFn,forall_exists_index,forall_apply_eq_imp_iff]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro i
  rw [M.orderDummyFilter_exact t _ _ _ x (r.2 i) (M.splitOrder_eval t raw x q r hr i)]
  exact Completion.test_eq_passed _ _ _ _ _ (fun _=>Iff.rfl) (r.2 i)

/-- The hard/ordinary/rare/dummy selection is on the actual retained split's
modulus and coin strings. The table is the same final retained complete log. -/
theorem retainedSplitFilter_exact {N P : ℕ} (hn : 128≤n) (t : ℕ)
    (raw : BooleanNetwork (M.width t) (FixedSplit.width n))
    (x : Basis c) (h : Trace n t) (q : Basis n) (r : UniversalSplit.Raw n)
    (hc : PhysicalTree.CompleteLog n N (M.dataLog x t h))
    (hP : P∈(M.dataLog x t h).map Prod.fst) (hP0 : P≠0)
    (hdiv : UniversalSplit.Hard (bitsValue q).toNat → (bitsValue q).toNat∣P)
    (hr : raw.eval (M.encoded x t h)=FixedSplit.encoding q r) :
    (M.retainedSplitFilter (by omega) t raw).eval (M.encoded x t h) 0=true ↔
      dataSplitPassed (trueData P) q (by omega) r := by
  classical
  rw [retainedSplitFilter,eval_bor,Bool.or_eq_true,eval_band,Bool.and_eq_true,
    eval_band,Bool.and_eq_true,bnot_value,UniversalSplit.hardOn_value hn,
    M.splitModulus_eval t raw _ q r hr,dataSplitPassed]
  by_cases hh : UniversalSplit.Hard (bitsValue q).toNat
  · simp only [hh,ite_eq_left,true_and,not_true_eq_false,false_and,or_false]
    rw [splitActualFilter,eval_band,Bool.and_eq_true,
      M.retainedListFilter_exact (by omega) t _ _ x h r.1 hc hP hP0 hh.1 (hdiv hh) hh.2.2.1
        (by rw [M.splitModulus_eval t raw _ q r hr]) (M.splitList_eval t raw _ q r hr),
      M.splitModulus_eval t raw _ q r hr,all_eval]
    simp only [List.mem_ofFn,forall_exists_index,forall_apply_eq_imp_iff]
    apply and_congr_right
    intro _
    apply forall_congr'
    intro i
    rw [M.retainedOrderFilter_exact (by omega) t _ _ _ x h (r.2 i) hc hP hP0
      (by rw [M.splitModulus_eval t raw _ q r hr];exact hh.1)
      (by rw [M.splitModulus_eval t raw _ q r hr];exact hdiv hh)
      (M.splitOrder_eval t raw _ q r hr i),M.splitBase_eval t raw _ q r hr,
      M.splitModulus_eval t raw _ q r hr]
  · simp only [hh,ite_eq_right,false_and,not_false_eq_true,true_and,false_or]
    exact M.splitDummyFilter_exact t raw _ q r hr
end NodeMachine
end ExactQuantumFactoring


end

end OAI
