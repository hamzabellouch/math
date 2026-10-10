import Mathlib
import OAI.Combinatorics.KMedian.Binary.BinaryLists

namespace OAI


                                      
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace ListFold
variable {α β : Type} (ea : α → List Bool) (eb : β → List Bool) (a0 : α)
variable (op : β × α → β)
abbrev enc : List α × β → List Bool := encodePair (encodeList ea) eb
 def body (s : List α × β) : β ⊕ (List α × β) :=
  if s.1.isEmpty then .inl s.2 else .inr (s.1.tail,op (s.2,s.1.head?.getD a0))
 def result (s : List α × β) : β := s.1.foldl (fun b a => op (b,a)) s.2

noncomputable def program (P : PolyProgram (encodePair eb ea) eb op) :
    PolyProgram (enc ea eb) (encodeLoop (enc ea eb) eb) (body a0 op) := by
  let px := PolyProgram.fst (encodeList ea) eb
  let py := PolyProgram.snd (encodeList ea) eb
  let hd := px.comp (PolyProgram.listHead ea a0)
  let tl := px.comp (PolyProgram.listTail ea a0)
  let newLast := (py.fanout hd).comp P
  let recur := (tl.fanout newLast).comp (PolyProgram.injectRight (enc ea eb) eb)
  let done := py.comp (PolyProgram.injectLeft (enc ea eb) eb)
  exact (PolyProgram.ite (px.comp (PolyProgram.listIsEmpty ea)) recur done).congr _ (fun _ => rfl)

 theorem run (as : List α) (b : β) (S : ℕ)
    (h : ∀ pre suf, as=pre++suf → (enc ea eb (suf,pre.foldl (fun b a => op (b,a)) b)).length ≤ S) :
    BoundedRun (enc ea eb) (body a0 op) S (as.length+1) (as,b) (result op (as,b)) := by
  induction as generalizing b with
  | nil =>
      apply BoundedRun.stop
      · exact h [] [] rfl
      · rfl
  | cons a as ih =>
      have hs : ∀ pre suf, as=pre++suf →
          (enc ea eb (suf,pre.foldl (fun b a => op (b,a)) (op (b,a)))).length ≤ S := by
        intro pre suf he
        exact h (a::pre) suf (by simp only [List.cons_append,he])
      exact BoundedRun.step (h [] (a::as) rfl) rfl (ih (op (b,a)) hs)

noncomputable def loop (P : PolyProgram (encodePair eb ea) eb op) (B : Polynomial ℕ)
    (hB : ∀ (as : List α) (b : β) pre suf, as=pre++suf →
      (eb (pre.foldl (fun b a => op (b,a)) b)).length ≤ B.eval (enc ea eb (as,b)).length) :
    PolyProgram (enc ea eb) eb (result op) :=
  (program ea eb a0 op P).loop (result op) (X+1) (2*X+1+B) (fun s => by
    refine ⟨s.1.length+1,?_,?_⟩
    · have h := EncodedList.length_le ea s.1
      simp only [eval_add,eval_X,eval_one,enc,encodePair_length]; omega
    · apply run
      intro pre suf he
      have hh := hB s.1 s.2 pre suf he
      have hx : (encodeList ea suf).length ≤ (encodeList ea s.1).length := by
        rw [he,EncodedList.append,List.length_append]
        omega
      simp only [enc,encodePair_length] at hh ⊢
      simp only [eval_add,eval_mul,eval_ofNat,eval_X,eval_one]
      omega)

 theorem linear_height (C : ℕ)
    (hop : ∀ b a, (eb (op (b,a))).length ≤ (eb b).length+C*(2*(ea a).length+1))
    (as : List α) (b : β) :
    (eb (as.foldl (fun b a => op (b,a)) b)).length ≤ (eb b).length+C*(encodeList ea as).length := by
  induction as generalizing b with
  | nil => simp only [List.foldl_nil,EncodedList.nil,List.length_nil,mul_zero,add_zero,le_refl]
  | cons a as ih =>
      have hh := ih (op (b,a))
      have ha := hop b a
      simp only [List.foldl_cons,EncodedList.cons_length]
      nlinarith

noncomputable def linearLoop (P : PolyProgram (encodePair eb ea) eb op) (C : ℕ)
    (hop : ∀ b a, (eb (op (b,a))).length ≤ (eb b).length+C*(2*(ea a).length+1)) :
    PolyProgram (enc ea eb) eb (result op) :=
  loop ea eb a0 op P ((Polynomial.C C+1)*X) (fun as b pre suf he => by
    have hh := linear_height ea eb op C hop pre b
    have hp : (encodeList ea pre).length ≤ (encodeList ea as).length := by
      rw [he,EncodedList.append,List.length_append]; omega
    simp only [eval_mul,eval_add,eval_C,eval_one,eval_X,enc,encodePair_length]
    nlinarith)
end ListFold

namespace PolyProgram
variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {op : β × α → β}
noncomputable def listFold (P : PolyProgram (encodePair eb ea) eb op) (a0 : α) (B : Polynomial ℕ)
    (hB : ∀ (as : List α) (b : β) pre suf, as=pre++suf →
      (eb (pre.foldl (fun b a => op (b,a)) b)).length ≤ B.eval (encodePair (encodeList ea) eb (as,b)).length) :
    PolyProgram (encodePair (encodeList ea) eb) eb (fun x => x.1.foldl (fun b a => op (b,a)) x.2) :=
  ListFold.loop ea eb a0 op P B hB
noncomputable def listFoldLinear (P : PolyProgram (encodePair eb ea) eb op) (a0 : α) (C : ℕ)
    (hop : ∀ b a, (eb (op (b,a))).length ≤ (eb b).length+C*(2*(ea a).length+1)) :
    PolyProgram (encodePair (encodeList ea) eb) eb (fun x => x.1.foldl (fun b a => op (b,a)) x.2) :=
  ListFold.linearLoop ea eb a0 op P C hop
end PolyProgram
end MetricKMedian.Binary
end

end OAI
