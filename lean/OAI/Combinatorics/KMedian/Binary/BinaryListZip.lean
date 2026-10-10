import Mathlib
import OAI.Combinatorics.KMedian.Binary.BooleanFinite
import OAI.Combinatorics.KMedian.Binary.BinaryLists
import OAI.Combinatorics.KMedian.Binary.BinaryListMap

namespace OAI


                                     
section
namespace MetricKMedian.Binary
open Function Polynomial
namespace ListZip
variable {α β : Type} (ea : α → List Bool) (eb : β → List Bool) (a0 : α) (b0 : β)
abbrev enc : (List α × List β) × List (α × β) → List Bool :=
  encodePair (encodePair (encodeList ea) (encodeList eb)) (encodeList (encodePair ea eb))
def body (x : (List α × List β) × List (α × β)) : List (α × β) ⊕ ((List α × List β) × List (α × β)) :=
  if x.1.1.isEmpty || x.1.2.isEmpty then .inl x.2.reverse
  else .inr ((x.1.1.tail,x.1.2.tail),(x.1.1.head?.getD a0,x.1.2.head?.getD b0)::x.2)
def result (x : (List α × List β) × List (α × β)) : List (α × β) := x.2.reverse++x.1.1.zip x.1.2
noncomputable def program : PolyProgram (enc ea eb) (encodeLoop (enc ea eb) (encodeList (encodePair ea eb))) (body a0 b0) := by
  let pair := PolyProgram.fst (encodePair (encodeList ea) (encodeList eb)) (encodeList (encodePair ea eb))
  let as := pair.comp (PolyProgram.fst (encodeList ea) (encodeList eb))
  let bs := pair.comp (PolyProgram.snd (encodeList ea) (encodeList eb))
  let cs := PolyProgram.snd (encodePair (encodeList ea) (encodeList eb)) (encodeList (encodePair ea eb))
  let test := (((as.comp (PolyProgram.listIsEmpty ea)).fanout (bs.comp (PolyProgram.listIsEmpty eb))).comp PolyProgram.boolOr)
  let done := ((cs.comp (PolyProgram.listReverse (encodePair ea eb) (a0,b0))).comp (PolyProgram.injectLeft (enc ea eb) (encodeList (encodePair ea eb))))
  let heads := (as.comp (PolyProgram.listHead ea a0)).fanout (bs.comp (PolyProgram.listHead eb b0))
  let tails := (as.comp (PolyProgram.listTail ea a0)).fanout (bs.comp (PolyProgram.listTail eb b0))
  let push := ((heads.fanout cs).comp (PolyProgram.listCons (encodePair ea eb)))
  let cont := ((tails.fanout push).comp (PolyProgram.injectRight (enc ea eb) (encodeList (encodePair ea eb))))
  exact (PolyProgram.ite test cont done).congr _ (fun _ => rfl)

 theorem run (as : List α) (bs : List β) (cs : List (α × β)) (S : ℕ)
    (hsize : (enc ea eb ((as,bs),cs)).length ≤ S) :
    ∃ t ≤ as.length+1, BoundedRun (enc ea eb) (body a0 b0) S t ((as,bs),cs) (result ((as,bs),cs)) := by
  induction as generalizing bs cs with
  | nil =>
      refine ⟨1,by simp,BoundedRun.stop hsize ?_⟩
      simp [body,result]
  | cons a as ih =>
      cases bs with
      | nil =>
          refine ⟨1,by simp,BoundedRun.stop hsize ?_⟩
          simp [body,result]
      | cons b bs =>
          have hs : (enc ea eb ((as,bs),(a,b)::cs)).length ≤ S := by
            simp only [enc,encodePair_length,EncodedList.cons_length] at hsize ⊢
            omega
          obtain ⟨t,ht,hr⟩ := ih bs ((a,b)::cs) hs
          refine ⟨t+1,by simpa only [List.length_cons] using Nat.succ_le_succ ht,?_⟩
          have he : result ((as,bs),(a,b)::cs)=result ((a::as,b::bs),cs) := by
            simp only [result,List.reverse_cons,List.zip_cons_cons,List.append_assoc,List.singleton_append]
          rw [← he]
          exact BoundedRun.step hsize (by simp [body]) hr

noncomputable def loop : PolyProgram (enc ea eb) (encodeList (encodePair ea eb)) result :=
  (program ea eb a0 b0).loop result (X+1) X (fun x => by
    obtain ⟨t,ht,hr⟩ := run ea eb a0 b0 x.1.1 x.1.2 x.2 (enc ea eb x).length le_rfl
    refine ⟨t,?_,?_⟩
    · have hh := EncodedList.length_le ea x.1.1
      simp only [eval_add,eval_X,eval_one,enc,encodePair_length]
      omega
    · simpa only [eval_X] using hr)
end ListZip
namespace PolyProgram
variable {α β γ : Type} (ea : α → List Bool) (eb : β → List Bool) (a0 : α) (b0 : β)
noncomputable def listZip : PolyProgram (encodePair (encodeList ea) (encodeList eb))
    (encodeList (encodePair ea eb)) (fun x : List α × List β => x.1.zip x.2) := by
  let start := (identity (encodePair (encodeList ea) (encodeList eb))).fanout
    (constant (encodePair (encodeList ea) (encodeList eb)) (encodeList (encodePair ea eb)) [])
  exact (start.comp (ListZip.loop ea eb a0 b0)).congr _ (fun _ => by simp only [Function.comp_apply,id_eq,ListZip.result,List.reverse_nil,List.nil_append])
noncomputable def listZipWith {ec : γ → List Bool} {f : α × β → γ}
    (P : PolyProgram (encodePair ea eb) ec f) :
    PolyProgram (encodePair (encodeList ea) (encodeList eb)) (encodeList ec) (fun x : List α × List β => (x.1.zip x.2).map f) :=
  ((listZip ea eb a0 b0).comp (P.listMap (a0,b0))).congr _ (fun _ => rfl)
end PolyProgram
end MetricKMedian.Binary
end

end OAI
