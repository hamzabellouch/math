import Mathlib
import OAI.Computability.Interspersed.Storage

namespace OAI

/-! Erasure of retained history symbols from work stacks. -/

noncomputable section
open scoped ContDiff
namespace PrefixFlows
namespace Interspersed
variable {Q A : Type*} {H : Set Q}
inductive Erases {G : Type*} (blank : A) : Stack (A ⊕ G) → Stack A → Prop
  | blank : Erases blank (fun _ => .inl blank) (fun _ => blank)
  | work (a : A) {L S} : Erases blank L S → Erases blank (push (.inl a) L) (push a S)
  | record (g : G) {L S} : Erases blank L S → Erases blank (push (.inr g) L) S

namespace Erases

variable {G : Type*} {blank : A}

 
theorem work_inv {a : A} {L : Stack (A ⊕ G)} {S : Stack A}
    (h : Erases blank (push (.inl a) L) S) :
    ∃ T, S = push a T ∧ Erases blank L T := by
  generalize he : push (Sum.inl a) L = K at h
  cases h with
  | blank =>
    have ha : a = blank := Sum.inl.inj (congrFun he 0)
    have hL : L = (fun _ => .inl blank) := funext (fun n => congrFun he (n + 1))
    subst a L
    exact ⟨(fun _ => blank), (push_constant blank).symm, .blank⟩
  | work b hT =>
    rcases push_inj.mp he with ⟨hab, rfl⟩
    have hab' : a = b := Sum.inl.inj hab
    subst b
    exact ⟨_, rfl, hT⟩
  | record g hT =>
    have hn : (Sum.inl a : A ⊕ G) = .inr g := congrFun he 0
    cases hn

 
theorem record_inv {g : G} {L : Stack (A ⊕ G)} {S : Stack A}
    (h : Erases blank (push (.inr g) L) S) : Erases blank L S := by
  generalize he : push (Sum.inr g) L = K at h
  cases h with
  | blank =>
    have hn : (Sum.inr g : A ⊕ G) = .inl blank := congrFun he 0
    cases hn
  | work a hT =>
    have hn : (Sum.inr g : A ⊕ G) = .inl a := congrFun he 0
    cases hn
  | record g' hT =>
    rcases push_inj.mp he with ⟨_, rfl⟩
    exact hT

theorem prepend_records (gs : List G) {L : Stack (A ⊕ G)} {S : Stack A}
    (h : Erases blank L S) : Erases blank (prepend (gs.map Sum.inr) L) S := by
  induction gs with
  | nil => exact h
  | cons g gs ih => exact .record g ih

theorem of_prepend_records (gs : List G) {L : Stack (A ⊕ G)} {S : Stack A}
    (h : Erases blank (prepend (gs.map Sum.inr) L) S) : Erases blank L S := by
  induction gs with
  | nil => exact h
  | cons g gs ih => exact ih h.record_inv

theorem prepend_work (w : List A) {L : Stack (A ⊕ G)} {S : Stack A}
    (h : Erases blank L S) :
    Erases blank (prepend (w.map Sum.inl) L) (prepend w S) := by
  induction w with
  | nil => exact h
  | cons a w ih => exact .work a ih

 
theorem eventually_blank {L : Stack (A ⊕ G)} {S : Stack A}
    (h : Erases blank L S) : ∃ n, BlankAfter (.inl blank) n L := by
  induction h with
  | blank => exact ⟨0, blankAfter_const _⟩
  | work a h ih =>
    rcases ih with ⟨n, hn⟩
    exact ⟨n + 1, blankAfter_push hn⟩
  | record g h ih =>
    rcases ih with ⟨n, hn⟩
    exact ⟨n + 1, blankAfter_push hn⟩

 
theorem eq_blank {L : Stack (A ⊕ G)} {S : Stack A}
    (h : Erases blank L S) (he : L = (fun _ => .inl blank)) :
    S = (fun _ => blank) := by
  revert he
  induction h with
  | blank => intro he; rfl
  | @work a L S h ih =>
    intro he
    have ha : a = blank := Sum.inl.inj (congrFun he 0)
    have hL : L = (fun _ => .inl blank) := funext (fun n => congrFun he (n + 1))
    rw [ha, ih hL, push_constant]
  | record g h ih =>
    intro he
    have hn : (Sum.inr g : A ⊕ G) = .inl blank := congrFun he 0
    cases hn

 
theorem deterministic {L : Stack (A ⊕ G)} {S T : Stack A}
    (h : Erases blank L S) (h' : Erases blank L T) : S = T := by
  induction h generalizing T with
  | blank => exact (h'.eq_blank rfl).symm
  | work a h ih =>
    rcases h'.work_inv with ⟨T', rfl, hT⟩
    rw [ih hT]
  | record g h ih => exact ih h'.record_inv

end Erases
end Interspersed
end PrefixFlows
end

end OAI
