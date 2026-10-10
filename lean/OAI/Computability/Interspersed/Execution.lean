import Mathlib
import OAI.Computability.Interspersed.Rules

namespace OAI

/-! Finite scans and simulation of individual work instructions. -/

noncomputable section
open scoped ContDiff
namespace PrefixFlows
namespace Interspersed
variable {Q A : Type*} {H : Set Q}
inductive Exec (δ : Q → A → Q × A × Move) : ℕ → Config Q A H → Config Q A H → Prop
  | zero (c) : Exec δ 0 c c
  | succ {n c d e} : Step δ c d → Exec δ n d e → Exec δ (n + 1) c e

 

theorem right_scan (δ : Q → A → Q × A × Move) (q : Q) (a : A)
    (gs : List (Record Q A H)) (L R : Stack (Symbol Q A H)) :
    Exec δ (gs.length + 1)
      (.scanRight q, L, prepend (gs.map Sum.inr) (push (.inl a) R))
      (.main q .right, prepend (gs.reverse.map Sum.inr) L, push (.inl a) R) := by
  induction gs generalizing L with
  | nil =>
    exact Exec.succ (Step.of_branch δ (.rightWork q a) L R) (Exec.zero _)
  | cons g gs ih =>
    have h := Exec.succ
      (Step.of_branch δ (.rightRecord q g) L (prepend (gs.map Sum.inr) (push (.inl a) R)))
      (ih (push (.inr g) L))
    simpa [source, target, List.reverse_cons, prepend_append] using h

 

theorem left_scan (δ : Q → A → Q × A × Move) (q : Q) (a : A)
    (gs : List (Record Q A H)) (L R : Stack (Symbol Q A H)) :
    Exec δ (gs.length + 1)
      (.scanLeft q, prepend (gs.map Sum.inr) (push (.inl a) L), R)
      (.main q .left, L, push (.inl a) (prepend (gs.reverse.map Sum.inr) R)) := by
  induction gs generalizing R with
  | nil =>
    exact Exec.succ (Step.of_branch δ (.leftWork q a) L R) (Exec.zero _)
  | cons g gs ih =>
    have h := Exec.succ
      (Step.of_branch δ (.leftRecord q g) (prepend (gs.map Sum.inr) (push (.inl a) L)) R)
      (ih (push (.inr g) R))
    simpa [source, target, List.reverse_cons, prepend_append] using h

 
theorem main_stay (δ : Q → A → Q × A × Move) (q : {q : Q // q ∉ H})
    (h : Move) (a b : A) (q' : Q) (hd : δ q a = (q', b, .stay))
    (L R : Stack (Symbol Q A H)) :
    Exec δ 1 (.main q h, L, push (.inl a) R)
      (.main q' .stay, push (.inr (q, h, a)) L, push (.inl b) R) := by
  have hs := Step.of_branch δ (.main q h a) L R
  simp only [source, target, hd] at hs
  exact Exec.succ hs (Exec.zero _)

 

theorem main_right (δ : Q → A → Q × A × Move) (q : {q : Q // q ∉ H})
    (h : Move) (a b c : A) (q' : Q) (hd : δ q a = (q', b, .right))
    (gs : List (Record Q A H)) (L R : Stack (Symbol Q A H)) :
    Exec δ (gs.length + 2)
      (.main q h, L, push (.inl a) (prepend (gs.map Sum.inr) (push (.inl c) R)))
      (.main q' .right,
        prepend (gs.reverse.map Sum.inr) (push (.inl b) (push (.inr (q, h, a)) L)),
        push (.inl c) R) := by
  have hs := Step.of_branch δ (.main q h a) L
    (prepend (gs.map Sum.inr) (push (.inl c) R))
  simp only [source, target, hd] at hs
  exact Exec.succ hs (right_scan δ q' c gs (push (.inl b) (push (.inr (q, h, a)) L)) R)

 

theorem main_left (δ : Q → A → Q × A × Move) (q : {q : Q // q ∉ H})
    (h : Move) (a b c : A) (q' : Q) (hd : δ q a = (q', b, .left))
    (gs : List (Record Q A H)) (L R : Stack (Symbol Q A H)) :
    Exec δ (gs.length + 2)
      (.main q h, prepend (gs.map Sum.inr) (push (.inl c) L), push (.inl a) R)
      (.main q' .left, L,
        push (.inl c) (prepend (gs.reverse.map Sum.inr) (push (.inl b) (push (.inr (q, h, a)) R)))) := by
  have hs := Step.of_branch δ (.main q h a)
    (prepend (gs.map Sum.inr) (push (.inl c) L)) R
  simp only [source, target, hd] at hs
  exact Exec.succ hs (left_scan δ q' c gs L (push (.inl b) (push (.inr (q, h, a)) R)))
end Interspersed
end PrefixFlows
end

end OAI
