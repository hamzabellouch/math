import Mathlib
import OAI.Combinatorics.KMedianRecovery.Branching.BranchBalls

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryClassFilter
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
variable {n m : ℕ}
def pack (S : Finset (Fin n)) (label : Fin n→Fin m) (c : Fin m) : List Bool :=
  pairBits (pairBits (BinaryFinSet.table label,c.val.bits),BinaryFinSet.encode S)
noncomputable def tag (x : List Bool) : List Bool := Lookup.run (pairBits (discardPrefix x,extractPrefix (extractPrefix x)))
noncomputable def tag_computes : PolyComputes tag :=
  (discardPrefix_computes.pair (extractPrefix_computes.comp extractPrefix_computes)).comp Lookup.run_computes
noncomputable def matching (x : List Bool) : Bool := WordEq.eq (pairBits (tag x,discardPrefix (extractPrefix x)))
noncomputable def matching_computes : PolyComputes (fun x=>[matching x]) :=
  (tag_computes.pair (extractPrefix_computes.comp discardPrefix_computes)).comp WordEq.eq_computes
noncomputable def run : List Bool→List Bool := filterWith matching
noncomputable def run_computes : PolyComputes run := filterWith_computes matching_computes
lemma run_pack (S : Finset (Fin n)) (label : Fin n→Fin m) (c : Fin m) :
    run (pack S label c)=BinaryFinSet.encode (S.filter (fun i=>label i=c)) := by
  simp only [run,pack,BinaryFinSet.encode_eq,filterWith_encode,List.filter_map,Function.comp_def,matching,tag,
    extractPrefix_pairBits,discardPrefix_pairBits,BinaryFinSet.table,lookup_ofFn,WordEq.eq_pair]
  have he (i : Fin n) : decide ((label i).val.bits=c.val.bits)=decide (label i=c) := by
    congr 1
    apply propext
    constructor
    · intro h
      apply Fin.ext
      simpa only [BinaryArithmetic.value_bits] using congrArg BinaryArithmetic.value h
    · exact fun h=>congrArg (fun j : Fin m=>j.val.bits) h
  simp_rw [he]
  rw [BinaryFinSet.filter_sort]
end MetricKMedianRecovery.BitMachine.BinaryClassFilter

end OAI
