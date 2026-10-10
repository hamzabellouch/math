import Mathlib
import OAI.Combinatorics.KMedian.CookLevin.TM2Locality

namespace OAI

section Inline_PCPTM2Response

namespace MetricKMedian.PCP.Tableau
open Turing.TM2 Function
open scoped Classical

abbrev BoundedList (A : Type) (r : ℕ) := {l : List A // l.length≤r}
namespace BoundedList
variable {A : Type} {r : ℕ}
def cells (l : BoundedList A r) : Fin r → Option A := fun i => l.val[i.val]?
lemma cells_injective : Function.Injective (cells (A := A) (r := r)) := by
  intro l m h
  apply Subtype.ext
  apply List.ext_getElem?
  intro i
  by_cases hi : i<r
  · exact congrFun h ⟨i,hi⟩
  · rw [List.getElem?_eq_none (l.property.trans (by omega)),
      List.getElem?_eq_none (m.property.trans (by omega))]
noncomputable instance [Fintype A] : Fintype (BoundedList A r) :=
  Fintype.ofInjective cells cells_injective
end BoundedList

variable {K : Type} {Γ : K → Type} {Λ σ : Type}
variable [DecidableEq K] [Fintype Λ]
variable (M : Λ → Stmt Γ Λ σ)
noncomputable def radius : ℕ := Finset.univ.sup (fun l => depth (M l))
omit [DecidableEq K] in
lemma depth_le (l : Λ) : depth (M l)≤radius M := by
  exact Finset.le_sup (f := fun l => depth (M l)) (Finset.mem_univ l)

def advance (c : Cfg Γ Λ σ) : Cfg Γ Λ σ :=
  match c.l with
  | none => c
  | some l => stepAux (M l) c.var c.stk

abbrev Control := Option Λ × σ
abbrev Prefix := ∀ k, BoundedList (Γ k) (radius M)
abbrev Response := Control (Λ := Λ) (σ := σ) × (∀ k, BoundedList (Γ k) (2*radius M))
noncomputable def respond (c : Control (Λ := Λ) (σ := σ)) (p : Prefix M) : Response M :=
  let next := advance M ⟨c.1,c.2,fun k => (p k).val⟩
  ⟨(next.l,next.var),fun k => ⟨next.stk k,by
    dsimp [next,advance]
    cases h : c.1 with
    | none => simpa [h] using (p k).property.trans (Nat.le_mul_of_pos_left _ (by omega))
    | some l =>
      exact (stepAux_length (M l) c.2 (fun j => (p j).val) k).trans
        (by have := (p k).property; have := depth_le M l; omega)⟩⟩

noncomputable def stackPrefix (S : ∀ k, List (Γ k)) : Prefix M :=
  fun k => ⟨(S k).take (radius M), by simp only [List.length_take]; exact min_le_left _ _⟩
lemma advance_stackPrefix (c : Cfg Γ Λ σ) :
    advance M c = appendCfg (advance M ⟨c.l,c.var,fun k => (stackPrefix M c.stk k).val⟩)
      (fun k => (c.stk k).drop (radius M)) := by
  cases h : c.l with
  | none =>
    cases c with
    | mk l v S =>
      simp only at h
      subst l
      simp only [advance,appendCfg,stackPrefix,List.take_append_drop]
  | some l =>
    simp only [advance,h,stackPrefix]
    exact stepAux_prefix (M l) (radius M) (depth_le M l) c.var c.stk

lemma response_control (c : Cfg Γ Λ σ) :
    ((advance M c).l,(advance M c).var)=(respond M (c.l,c.var) (stackPrefix M c.stk)).1 := by
  rw [advance_stackPrefix]
  rfl
lemma response_stack (c : Cfg Γ Λ σ) (k : K) :
    (advance M c).stk k=((respond M (c.l,c.var) (stackPrefix M c.stk)).2 k).val ++
      (c.stk k).drop (radius M) := by
  rw [advance_stackPrefix]
  rfl

lemma response_cell (c : Cfg Γ Λ σ) (k : K) (i : ℕ) :
    ((advance M c).stk k)[i]? =
      let p := (respond M (c.l,c.var) (stackPrefix M c.stk)).2 k
      if i<p.val.length then p.val[i]? else (c.stk k)[radius M+(i-p.val.length)]? := by
  rw [response_stack]
  dsimp only
  split_ifs with h
  · exact List.getElem?_append_left h
  · rw [List.getElem?_append_right (by omega),List.getElem?_drop]

lemma advance_length (c : Cfg Γ Λ σ) (k : K) :
    ((advance M c).stk k).length ≤ (c.stk k).length+radius M := by
  cases h : c.l with
  | none => simp [advance,h]
  | some l =>
    simp only [advance,h]
    exact (stepAux_length (M l) c.var c.stk k).trans (Nat.add_le_add_left (depth_le M l) _)
end MetricKMedian.PCP.Tableau

end Inline_PCPTM2Response

end OAI
