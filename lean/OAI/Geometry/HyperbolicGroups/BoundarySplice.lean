import Mathlib
import OAI.Geometry.HyperbolicGroups.BoundaryList

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D]

lemma formPerm_append_join (l : List D) (a b : D) (r : List D) :
    (l++a::b::r).formPerm = (l++[a]).formPerm * swap a b * (b::r).formPerm := by
  induction l with
  | nil => simp only [List.nil_append,List.formPerm_singleton,one_mul,List.formPerm_cons_cons]
  | cons x l ih =>
    cases l with
    | nil => simp only [List.cons_append,List.nil_append,List.formPerm_cons_cons,List.formPerm_singleton,mul_one,mul_assoc]
    | cons y l =>
      simp only [List.cons_append,List.formPerm_cons_cons] at ih ⊢
      rw [ih]; simp only [mul_assoc]

namespace IsBoundary
variable {f : Perm D} {l r : List D} {a b : D}

/-- Concatenation is the literal connected-sum splice at the two incoming
corners. The side order, not merely the freely represented word, is retained. -/
theorem splice_append (hl : IsBoundary f (l++[a])) (hr : IsBoundary f (b::r))
    (hd : ∀ x ∈ l++[a], x ∉ b::r) :
    IsBoundary (f * swap a ((b::r).getLast (by simp))) ((l++[a])++(b::r)) := by
  let xs := l++[a]
  let ys := b::r
  let c := ys.getLast (by simp [ys])
  have ha : a ∈ xs := by simp [xs]
  have hc : c ∈ ys := List.getLast_mem _
  have hdis : ∀ x ∈ xs, x ∉ ys := hd
  have hn : (xs++ys).Nodup := by
    rw [List.nodup_append]
    exact ⟨hl.nodup,hr.nodup,fun x hx y hy he => hdis x hx (he ▸ hy)⟩
  have hform : (xs++ys).formPerm = xs.formPerm * ys.formPerm * swap a c := by
    have hz : ys.formPerm a = a := List.formPerm_apply_of_notMem (hdis a ha)
    have hy : ys.formPerm c = b := List.formPerm_apply_getLast b r
    have hs : ys.formPerm * swap a c = swap a b * ys.formPerm := by
      rw [mul_swap_eq_swap_mul,hz,hy]
    dsimp only [xs,ys]
    rw [List.append_assoc]
    change (l++a::b::r).formPerm = (l++[a]).formPerm * (b::r).formPerm * swap a c
    rw [formPerm_append_join]
    simp only [mul_assoc]
    rw [hs]
  have ht : ∀ x ∈ xs++ys, f x = (xs.formPerm*ys.formPerm) x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · rw [mul_apply,List.formPerm_apply_of_notMem (hdis x hx),hl.turn x hx]
    · have hn : ys.formPerm x ∉ xs := by
        intro hh
        exact hdis _ hh (List.formPerm_apply_mem_of_mem hx)
      rw [mul_apply,List.formPerm_apply_of_notMem hn,hr.turn x hx]
  refine ⟨hn,?_⟩
  intro x hx
  have hs : swap a c x ∈ xs++ys := by
    by_cases he : x = a
    · subst x; rw [swap_apply_left]; exact List.mem_append_right xs hc
    by_cases hf : x = c
    · subst x; rw [swap_apply_right]; exact List.mem_append_left ys ha
    · rwa [swap_apply_of_ne_of_ne he hf]
  change f (swap a c x) = (xs++ys).formPerm x
  rw [ht _ hs,hform]; rfl

end IsBoundary
end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
