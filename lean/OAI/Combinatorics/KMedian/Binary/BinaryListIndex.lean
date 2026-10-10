import Mathlib
import OAI.Combinatorics.KMedian.Binary.BinaryLists
import OAI.Combinatorics.KMedian.Binary.BinaryNatural
import OAI.Combinatorics.KMedian.Binary.BinarySubtraction

namespace OAI


                                       
section
namespace MetricKMedian.Binary
open Function Polynomial
namespace ListSplit
variable {α : Type} (ea : α → List Bool) (a0 : α)
abbrev enc : List α × (ℕ × List α) → List Bool := encodePair (encodeList ea) (encodePair Nat.bits (encodeList ea))
abbrev out : List α × List α → List Bool := encodePair (encodeList ea) (encodeList ea)
def body (x : List α × (ℕ × List α)) : (List α × List α) ⊕ (List α × (ℕ × List α)) :=
  if x.1.isEmpty || decide (x.2.1=0) then .inl (x.2.2.reverse,x.1)
  else .inr (x.1.tail,(x.2.1-1,x.1.head?.getD a0::x.2.2))
def result (x : List α × (ℕ × List α)) : List α × List α := (x.2.2.reverse++x.1.take x.2.1,x.1.drop x.2.1)
noncomputable def program : PolyProgram (enc ea) (encodeLoop (enc ea) (out ea)) (body a0) := by
  let ls := PolyProgram.fst (encodeList ea) (encodePair Nat.bits (encodeList ea))
  let ns := PolyProgram.snd (encodeList ea) (encodePair Nat.bits (encodeList ea))
  let n := ns.comp (PolyProgram.fst Nat.bits (encodeList ea))
  let bs := ns.comp (PolyProgram.snd Nat.bits (encodeList ea))
  let zero := (((ls.comp (PolyProgram.listIsEmpty ea)).fanout (n.comp PolyProgram.natZero)).comp PolyProgram.boolOr)
  let done := (((bs.comp (PolyProgram.listReverse ea a0)).fanout ls).comp (PolyProgram.injectLeft (enc ea) (out ea)))
  let pred := ((n.fanout (PolyProgram.constant (enc ea) Nat.bits 1)).comp PolyProgram.natSub)
  let push := (((ls.comp (PolyProgram.listHead ea a0)).fanout bs).comp (PolyProgram.listCons ea))
  let cont := (((ls.comp (PolyProgram.listTail ea a0)).fanout (pred.fanout push)).comp (PolyProgram.injectRight (enc ea) (out ea)))
  exact (PolyProgram.ite zero cont done).congr _ (fun _ => rfl)

 theorem run (as bs : List α) (n S : ℕ) (hsize : (enc ea (as,(n,bs))).length ≤ S) :
    ∃ t ≤ as.length+1, BoundedRun (enc ea) (body a0) S t (as,(n,bs)) (result (as,(n,bs))) := by
  induction as generalizing n bs with
  | nil =>
      refine ⟨1,by simp,BoundedRun.stop hsize ?_⟩
      simp only [body,result,List.isEmpty_nil,Bool.true_or,List.take_nil,List.drop_nil,List.append_nil]
      rfl
  | cons a as ih =>
      cases n with
      | zero =>
          refine ⟨1,by simp,BoundedRun.stop hsize ?_⟩
          simp only [body,result,List.isEmpty_cons,decide_true,Bool.false_or,List.take_zero,List.drop_zero,List.append_nil]
          rfl
      | succ n =>
          have hn := NatBinary.length_mono (Nat.le_succ n)
          change n.bits.length ≤ (n+1).bits.length at hn
          have hs : (enc ea (as,(n,a::bs))).length ≤ S := by
            simp only [enc,encodePair_length,EncodedList.cons_length] at hsize ⊢
            omega
          obtain ⟨t,ht,hr⟩ := ih (a::bs) n hs
          refine ⟨t+1,by simpa only [List.length_cons] using Nat.succ_le_succ ht,?_⟩
          have hb : body a0 (a::as,(n+1,bs))=.inr (as,(n,a::bs)) := by simp [body]
          have he : result (as,(n,a::bs))=result (a::as,(n+1,bs)) := by
            simp only [result,List.reverse_cons,List.take_succ_cons,List.drop_succ_cons,List.append_assoc,List.singleton_append]
          rw [← he]
          exact BoundedRun.step hsize hb hr

noncomputable def loop : PolyProgram (enc ea) (out ea) result :=
  (program ea a0).loop result (X+1) X (fun x => by
    obtain ⟨t,ht,hr⟩ := run ea a0 x.1 x.2.2 x.2.1 (enc ea x).length le_rfl
    refine ⟨t,?_,?_⟩
    · have hh := EncodedList.length_le ea x.1
      simp only [eval_add,eval_X,eval_one,enc,encodePair_length]
      omega
    · simpa only [eval_X] using hr)
end ListSplit

namespace PolyProgram
variable {α : Type} (ea : α → List Bool) (a0 : α)
noncomputable def listSplitAt : PolyProgram (encodePair (encodeList ea) Nat.bits)
    (encodePair (encodeList ea) (encodeList ea)) (fun x : List α × ℕ => (x.1.take x.2,x.1.drop x.2)) := by
  let ls := fst (encodeList ea) Nat.bits
  let n := snd (encodeList ea) Nat.bits
  let start := ls.fanout (n.fanout (constant (encodePair (encodeList ea) Nat.bits) (encodeList ea) []))
  exact (start.comp (ListSplit.loop ea a0)).congr _ (fun x => by simp only [Function.comp_apply,ListSplit.result,List.reverse_nil,List.nil_append])
noncomputable def listTake : PolyProgram (encodePair (encodeList ea) Nat.bits)
    (encodeList ea) (fun x : List α × ℕ => x.1.take x.2) :=
  ((listSplitAt ea a0).comp (fst (encodeList ea) (encodeList ea))).congr _ (fun _ => rfl)
noncomputable def listDrop : PolyProgram (encodePair (encodeList ea) Nat.bits)
    (encodeList ea) (fun x : List α × ℕ => x.1.drop x.2) :=
  ((listSplitAt ea a0).comp (snd (encodeList ea) (encodeList ea))).congr _ (fun _ => rfl)
noncomputable def listGetD : PolyProgram (encodePair (encodeList ea) Nat.bits)
    ea (fun x : List α × ℕ => x.1[x.2]?.getD a0) := by
  exact ((listDrop ea a0).comp (listHead ea a0)).congr _ (fun x => by
    simp only [Function.comp_apply,List.head?_drop])
noncomputable def listEraseIdx : PolyProgram (encodePair (encodeList ea) Nat.bits)
    (encodeList ea) (fun x : List α × ℕ => x.1.take x.2++(x.1.drop x.2).tail) :=
  (((listSplitAt ea a0).comp ((listTail ea a0).second (encodeList ea))).comp (listAppend ea a0)).congr _ (fun _ => rfl)
noncomputable def listInsertAt : PolyProgram (encodePair (encodePair (encodeList ea) Nat.bits) ea)
    (encodeList ea) (fun x : (List α × ℕ) × α => x.1.1.take x.1.2++x.2::x.1.1.drop x.1.2) := by
  let sp := (fst (encodePair (encodeList ea) Nat.bits) ea).comp (listSplitAt ea a0)
  let pre := sp.comp (fst (encodeList ea) (encodeList ea))
  let suf := sp.comp (snd (encodeList ea) (encodeList ea))
  let elem := snd (encodePair (encodeList ea) Nat.bits) ea
  exact ((pre.fanout ((elem.fanout suf).comp (listCons ea))).comp (listAppend ea a0)).congr _ (fun _ => rfl)
end PolyProgram
end MetricKMedian.Binary
end

end OAI
