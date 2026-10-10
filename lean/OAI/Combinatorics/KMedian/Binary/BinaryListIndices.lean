import Mathlib
import OAI.Combinatorics.KMedian.Binary.BinaryListFold
import OAI.Combinatorics.KMedian.Binary.BinaryLists
import OAI.Combinatorics.KMedian.Binary.BinaryRationalHeight

namespace OAI


                                         
section
namespace MetricKMedian.Binary
open Function Polynomial
namespace ListAlgorithms
variable {α : Type}
def indexStep (x : (ℕ × List ℕ) × α) : ℕ × List ℕ := (x.1.1+1,x.1.1::x.1.2)
 theorem pushIndices (xs : List α) (n : ℕ) (bs : List ℕ) :
    xs.foldl (fun b a => indexStep (b,a)) (n,bs)=
      (n+xs.length,(List.range' n xs.length).reverse++bs) := by
  induction xs generalizing n bs with
  | nil => simp
  | cons a xs ih =>
      change xs.foldl (fun b a => indexStep (b,a)) (n+1,n::bs)=_
      rw [ih]
      simp only [List.length_cons,List.range'_succ,List.reverse_cons,List.append_assoc,List.singleton_append]
      congr 1
      omega
 theorem index_partial_size (ea : α → List Bool) (xs : List α) (x : ℕ × List ℕ) (pre suf : List α)
    (he : xs=pre++suf) :
    (encodePair Nat.bits (encodeList Nat.bits) (pre.foldl (fun b a => indexStep (b,a)) x)).length ≤
      10*((encodePair (encodeList ea) (encodePair Nat.bits (encodeList Nat.bits)) (xs,x)).length+1)^2 := by
  let L := (encodePair (encodeList ea) (encodePair Nat.bits (encodeList Nat.bits)) (xs,x)).length
  have hp : pre.length ≤ L := by
    have hp : (encodeList ea pre).length ≤ (encodeList ea xs).length := by rw [he,EncodedList.append,List.length_append]; omega
    have hh := EncodedList.length_le ea pre
    simp only [L,encodePair_length]; omega
  have hn : x.1.bits.length ≤ L := by simp only [L,encodePair_length]; omega
  have hb : (encodeList Nat.bits x.2).length ≤ L := by simp only [L,encodePair_length]; omega
  have hl : pre.length.bits.length ≤ pre.length+1 := NatBinary.length_le_height (Nat.lt_two_pow_self.le)
  have hc := NatBinary.add_length x.1 pre.length
  have hi : ∀ q∈List.range' x.1 pre.length, q.bits.length ≤ 2*L+2 := by
    intro q hq
    have hq' : q ≤ x.1+pre.length := (List.mem_range'_1.mp hq).2.le
    have hh := (NatBinary.length_mono hq').trans hc
    omega
  have hr := EncodedList.length_bound Nat.bits (List.range' x.1 pre.length) (2*L+2) hi
  simp only [List.length_range'] at hr
  have hcount : (x.1+pre.length).bits.length ≤ 2*L+2 := by omega
  have hr' : (encodeList Nat.bits (List.range' x.1 pre.length)).length ≤ L*(4*L+5) := by
    calc
      _ ≤ pre.length*(2*(2*L+2)+1) := hr
      _ ≤ L*(2*(2*L+2)+1) := Nat.mul_le_mul_right _ hp
      _ = L*(4*L+5) := by ring
  change (encodePair Nat.bits (encodeList Nat.bits) (pre.foldl (fun b a => indexStep (b,a)) (x.1,x.2))).length ≤ _
  rw [pushIndices]
  simp only [encodePair_length,EncodedList.append,List.length_append,EncodedList.reverse_length]
  simp only [L,encodePair_length] at hcount hr' hb
  nlinarith

end ListAlgorithms
namespace PolyProgram
variable {α : Type} (ea : α → List Bool) (a0 : α)
noncomputable def listIndices : PolyProgram (encodeList ea) (encodeList Nat.bits) (fun xs : List α => List.range xs.length) := by
  let eb := encodePair Nat.bits (encodeList Nat.bits)
  let acc := fst eb ea
  let n := acc.comp (fst Nat.bits (encodeList Nat.bits))
  let bs := acc.comp (snd Nat.bits (encodeList Nat.bits))
  let inc := (n.fanout (constant (encodePair eb ea) Nat.bits 1)).comp natAdd
  let push := (n.fanout bs).comp (listCons Nat.bits)
  let step : PolyProgram (encodePair eb ea) eb ListAlgorithms.indexStep :=
    (inc.fanout push).congr _ (fun _ => rfl)
  let fold := step.listFold a0 (10*(X+1)^2) (by
    intro xs x pre suf he
    simpa only [eval_mul,eval_ofNat,eval_pow,eval_add,eval_X,eval_one] using ListAlgorithms.index_partial_size ea xs x pre suf he)
  let start := (identity (encodeList ea)).fanout (constant (encodeList ea) eb (0,[]))
  exact ((((start.comp fold).comp (snd Nat.bits (encodeList Nat.bits))).comp (listReverse Nat.bits 0))).congr _ (fun xs => by
    simp only [Function.comp_apply,id_eq,ListAlgorithms.pushIndices,List.append_nil,List.reverse_reverse,← List.range_eq_range'])
end PolyProgram
end MetricKMedian.Binary
end

end OAI
