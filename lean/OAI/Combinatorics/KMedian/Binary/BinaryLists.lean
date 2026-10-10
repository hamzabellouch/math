import Mathlib
import OAI.Combinatorics.KMedian.Binary.BooleanThread
import OAI.Combinatorics.KMedian.Binary.BooleanProducts
import OAI.Combinatorics.KMedian.Binary.BooleanListPrimitives
import OAI.Combinatorics.KMedian.Binary.BooleanRecode

namespace OAI


                                   
section
namespace MetricKMedian.Binary
open Function Polynomial

 def encodeList {α : Type} (ea : α → List Bool) : List α → List Bool
  | [] => []
  | a::as => quote (ea a)++encodeList ea as

namespace EncodedList
variable {α : Type} (ea : α → List Bool)
 theorem nil : encodeList ea []=[] := rfl
 theorem cons (a : α) (as : List α) : encodeList ea (a::as)=quote (ea a)++encodeList ea as := rfl
 theorem cons_length (a : α) (as : List α) : (encodeList ea (a::as)).length=2*(ea a).length+1+(encodeList ea as).length := by
  simp only [encodeList,List.length_append,quote_length]
 theorem length_le (as : List α) : as.length ≤ (encodeList ea as).length := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [cons_length,List.length_cons]; omega
 theorem isEmpty (as : List α) : (encodeList ea as).isEmpty=as.isEmpty := by
  cases as with
  | nil => rfl
  | cons a as =>
      have h := cons_length ea a as
      apply List.isEmpty_eq_false_iff.mpr
      intro hz
      simp only [hz,List.length_nil] at h
      omega
 theorem append (as bs : List α) : encodeList ea (as++bs)=encodeList ea as++encodeList ea bs := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [List.cons_append,encodeList,ih,List.append_assoc]
 theorem reverse_length (as : List α) : (encodeList ea as.reverse).length=(encodeList ea as).length := by
  induction as with
  | nil => rfl
  | cons a as ih =>
      simp only [List.reverse_cons,append,List.length_append,cons_length,nil,List.length_nil,ih]
      omega
 theorem member_length (as : List α) (a : α) (h : a∈as) : (ea a).length ≤ (encodeList ea as).length := by
  induction as with
  | nil => simp at h
  | cons b as ih =>
      simp only [List.mem_cons] at h
      rcases h with rfl|h
      · rw [cons_length]; omega
      · have hh := ih h
        rw [cons_length]; omega
 theorem length_bound (as : List α) (L : ℕ) (h : ∀ a∈as, (ea a).length ≤ L) :
    (encodeList ea as).length ≤ as.length*(2*L+1) := by
  induction as with
  | nil => simp only [nil,List.length_nil,zero_mul,le_refl]
  | cons a as ih =>
      have ha := h a (by simp)
      have hh := ih (fun a ha => h a (by simp [ha]))
      rw [cons_length,List.length_cons]
      nlinarith
end EncodedList

namespace PolyProgram
variable {α : Type} (ea : α → List Bool) (a0 : α)
noncomputable def listIsEmpty : PolyProgram (encodeList ea) encodeBool List.isEmpty :=
  isEmpty.recode (encodeList ea) (fun _ => rfl) (fun as => by rw [EncodedList.isEmpty])

noncomputable def listUncons : PolyProgram (encodeList ea) (encodePair ea (encodeList ea))
    (fun as => (as.head?.getD a0,as.tail)) := by
  let raw : PolyProgram (encodeList ea) id (encodeList ea) := (identity id).recode (encodeList ea) (fun _ => rfl) (fun _ => rfl)
  let deflt := constant (encodeList ea) id (Binary.quote (ea a0))
  refine (ite (listIsEmpty ea) raw deflt).recode id (fun _ => rfl) ?_
  intro as
  cases as with
  | nil => simp [encodePair,encodeList]
  | cons a as => rfl
noncomputable def listHead : PolyProgram (encodeList ea) ea (fun as => as.head?.getD a0) :=
  ((listUncons ea a0).comp (fst ea (encodeList ea))).congr _ (fun _ => rfl)
noncomputable def listTail : PolyProgram (encodeList ea) (encodeList ea) List.tail :=
  ((listUncons ea a0).comp (snd ea (encodeList ea))).congr _ (fun _ => rfl)
noncomputable def listCons : PolyProgram (encodePair ea (encodeList ea)) (encodeList ea) (fun x => x.1::x.2) :=
  (identity id).recode (encodePair ea (encodeList ea)) (fun _ => rfl) (fun _ => rfl)
end PolyProgram

namespace ListReverse
variable {α : Type} (ea : α → List Bool) (a0 : α)
abbrev enc : List α × List α → List Bool := encodePair (encodeList ea) (encodeList ea)
 def body (s : List α × List α) : List α ⊕ (List α × List α) :=
  if s.1.isEmpty then .inl s.2 else .inr (s.1.tail,s.1.head?.getD a0::s.2)
 def result (s : List α × List α) : List α := s.1.reverse++s.2

noncomputable def program : PolyProgram (enc ea) (encodeLoop (enc ea) (encodeList ea)) (body a0) := by
  let px := PolyProgram.fst (encodeList ea) (encodeList ea)
  let py := PolyProgram.snd (encodeList ea) (encodeList ea)
  let hd := px.comp (PolyProgram.listHead ea a0)
  let tl := px.comp (PolyProgram.listTail ea a0)
  let newLast := (hd.fanout py).comp (PolyProgram.listCons ea)
  let recur := (tl.fanout newLast).comp (PolyProgram.injectRight (enc ea) (encodeList ea))
  let done := py.comp (PolyProgram.injectLeft (enc ea) (encodeList ea))
  exact (PolyProgram.ite (px.comp (PolyProgram.listIsEmpty ea)) recur done).congr _ (fun _ => rfl)

 theorem run (as bs : List α) (S : ℕ) (h : 2*(encodeList ea as).length+1+(encodeList ea bs).length ≤ S) :
    BoundedRun (enc ea) (body a0) S (as.length+1) (as,bs) (as.reverse++bs) := by
  induction as generalizing bs with
  | nil =>
      apply BoundedRun.stop
      · simpa only [enc,encodePair_length] using h
      · rfl
  | cons a as ih =>
      have hs : 2*(encodeList ea as).length+1+(encodeList ea (a::bs)).length ≤ S := by
        simp only [EncodedList.cons_length] at h ⊢
        omega
      have hr := BoundedRun.step (ea:=enc ea) (f:=body a0)
        (a:=(a::as,bs)) (a':=(as,a::bs))
        (by simpa only [enc,encodePair_length] using h) rfl (ih (a::bs) hs)
      simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using hr

noncomputable def loop : PolyProgram (enc ea) (encodeList ea) result :=
  (program ea a0).loop result (X+1) X (fun s => by
    refine ⟨s.1.length+1,?_,?_⟩
    · have h := EncodedList.length_le ea s.1
      simp only [eval_add,eval_X,eval_one,enc,encodePair_length]; omega
    · simpa only [eval_X,enc,encodePair_length,result] using run ea a0 s.1 s.2
        (2*(encodeList ea s.1).length+1+(encodeList ea s.2).length) le_rfl)
end ListReverse

namespace PolyProgram
variable {α : Type} (ea : α → List Bool) (a0 : α)
noncomputable def listReverse : PolyProgram (encodeList ea) (encodeList ea) List.reverse :=
  (((identity (encodeList ea)).fanout (constant (encodeList ea) (encodeList ea) [])).comp (ListReverse.loop ea a0)).congr _
    (fun _ => List.append_nil _)
noncomputable def listAppend : PolyProgram (encodePair (encodeList ea) (encodeList ea)) (encodeList ea) (fun x => x.1++x.2) :=
  (((listReverse ea a0).thread (encodeList ea)).comp (ListReverse.loop ea a0)).congr _
    (fun _ => by simp only [Function.comp_apply,ListReverse.result,List.reverse_reverse])
end PolyProgram
end MetricKMedian.Binary
end

end OAI
