import Mathlib
import OAI.Combinatorics.KMedian.Binary.BinaryLists
import OAI.Combinatorics.KMedian.Binary.BinaryAddition
import OAI.Combinatorics.KMedian.Binary.BinaryNatural
import OAI.Combinatorics.KMedian.Binary.BinaryListFold

namespace OAI


                                           
section
namespace MetricKMedian.Binary
open Function Polynomial
namespace ListFindIdx
variable {α : Type} (ea : α → List Bool) (a0 : α) (p : α → Bool)
abbrev enc : List α × ℕ → List Bool := encodePair (encodeList ea) Nat.bits
def body (x : List α × ℕ) : ℕ ⊕ (List α × ℕ) :=
  if x.1.isEmpty || p (x.1.head?.getD a0) then .inl x.2 else .inr (x.1.tail,x.2+1)
def result (x : List α × ℕ) : ℕ := x.2+x.1.findIdx p
noncomputable def program (P : PolyProgram ea encodeBool p) :
    PolyProgram (enc ea) (encodeLoop (enc ea) Nat.bits) (body a0 p) := by
  let ls := PolyProgram.fst (encodeList ea) Nat.bits
  let n := PolyProgram.snd (encodeList ea) Nat.bits
  let hd := (ls.comp (PolyProgram.listHead ea a0)).comp P
  let test := ((ls.comp (PolyProgram.listIsEmpty ea)).fanout hd).comp PolyProgram.boolOr
  let done := n.comp (PolyProgram.injectLeft (enc ea) Nat.bits)
  let inc := (n.fanout (PolyProgram.constant (enc ea) Nat.bits 1)).comp PolyProgram.natAdd
  let cont := (((ls.comp (PolyProgram.listTail ea a0)).fanout inc).comp (PolyProgram.injectRight (enc ea) Nat.bits))
  exact (PolyProgram.ite test cont done).congr _ (fun _ => rfl)
 theorem run (as : List α) (n S : ℕ) (hsize : (enc ea (as,n)).length ≤ S) :
    ∃ t ≤ as.length+1, BoundedRun (enc ea) (body a0 p) S t (as,n) (result p (as,n)) := by
  induction as generalizing n with
  | nil =>
      refine ⟨1,by simp,BoundedRun.stop hsize ?_⟩
      simp [body,result]
  | cons a as ih =>
      cases hp : p a with
      | true =>
          refine ⟨1,by simp,BoundedRun.stop hsize ?_⟩
          simp [body,result,hp,List.findIdx_cons]
      | false =>
          have hn := NatBinary.add_length n 1
          have hs : (enc ea (as,n+1)).length ≤ S := by
            have hone : (1:ℕ).bits.length=1 := rfl
            rw [hone] at hn
            simp only [enc,encodePair_length,EncodedList.cons_length] at hsize ⊢
            omega
          obtain ⟨t,ht,hr⟩ := ih (n+1) hs
          refine ⟨t+1,by simpa only [List.length_cons] using Nat.succ_le_succ ht,?_⟩
          have he : result p (as,n+1)=result p (a::as,n) := by simp [result,List.findIdx_cons,hp,Nat.add_comm,Nat.add_left_comm]
          rw [← he]
          exact BoundedRun.step hsize (by simp [body,hp]) hr
noncomputable def loop (P : PolyProgram ea encodeBool p) : PolyProgram (enc ea) Nat.bits (result p) :=
  (program ea a0 p P).loop (result p) (X+1) X (fun x => by
    obtain ⟨t,ht,hr⟩ := run ea a0 p x.1 x.2 (enc ea x).length le_rfl
    refine ⟨t,?_,?_⟩
    · have hh := EncodedList.length_le ea x.1
      simp only [eval_add,eval_X,eval_one,enc,encodePair_length]
      omega
    · simpa only [eval_X] using hr)
end ListFindIdx
namespace ListAlgorithms
variable {α : Type}
 theorem foldChoice (p : α × α → Bool) (as : List α) (b : α) :
    as.foldl (fun b a => if p (b,a) then a else b) b=b ∨ as.foldl (fun b a => if p (b,a) then a else b) b∈as := by
  induction as generalizing b with
  | nil => exact Or.inl rfl
  | cons a as ih =>
      simp only [List.foldl_cons]
      cases hp : p (b,a)
      · simpa only [hp,Bool.false_eq_true,ite_false] using (ih b).imp_right (fun h => List.mem_cons_of_mem _ h)
      · simp only [ite_true]
        rcases ih a with he|hmem
        · exact Or.inr (by rw [he]; exact List.mem_cons_self)
        · exact Or.inr (List.mem_cons_of_mem _ hmem)
end ListAlgorithms
namespace PolyProgram
variable {α : Type} {ea : α → List Bool}
noncomputable def listFindIdx {p : α → Bool} (P : PolyProgram ea encodeBool p) (a0 : α) :
    PolyProgram (encodeList ea) Nat.bits (List.findIdx p) :=
  ((((identity (encodeList ea)).fanout (constant (encodeList ea) Nat.bits 0)).comp
    (ListFindIdx.loop ea a0 p P))).congr _ (fun _ => by simp only [Function.comp_apply,id_eq,ListFindIdx.result,Nat.zero_add])
noncomputable def listChoose {p : α × α → Bool} (P : PolyProgram (encodePair ea ea) encodeBool p) (a0 : α) :
    PolyProgram (encodePair (encodeList ea) ea) ea
      (fun x : List α × α => x.1.foldl (fun b a => if p (b,a) then a else b) x.2) := by
  let step : PolyProgram (encodePair ea ea) ea (fun x => if p x then x.2 else x.1) :=
    (ite P (fst ea ea) (snd ea ea)).congr _ (fun _ => rfl)
  exact step.listFold a0 X (fun as b pre suf he => by
    rcases ListAlgorithms.foldChoice p pre b with h|h
    · rw [h]
      simp only [eval_X,encodePair_length]; omega
    · have hp : (encodeList ea pre).length ≤ (encodeList ea as).length := by
        rw [he,EncodedList.append,List.length_append]; omega
      have hh := (EncodedList.member_length ea pre _ h).trans hp
      simp only [eval_X,encodePair_length]; omega)
end PolyProgram
end MetricKMedian.Binary
end

end OAI
