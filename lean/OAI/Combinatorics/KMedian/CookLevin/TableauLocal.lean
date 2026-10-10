import Mathlib
import OAI.Combinatorics.KMedian.CookLevin.TM2Response
import OAI.Combinatorics.KMedian.CookLevin.TableauRows

namespace OAI

section Inline_PCPTableauLocal

namespace MetricKMedian.PCP.Tableau
open Turing.TM2 Function
open scoped Classical

variable {K : Type} {Γ : K → Type} {Λ σ : Type}
variable [DecidableEq K] [Fintype Λ]
variable (M : Λ → Stmt Γ Λ σ)

abbrev Tops := ∀ k, Fin (radius M) → Option (Γ k)
def PrefixRelation (c : Control (Λ := Λ) (σ := σ)) (tops : Tops M) (r : Response M) : Prop :=
  ∃ p : Prefix M, (∀ k, BoundedList.cells (p k)=tops k) ∧ r=respond M c p
lemma prefixRelation_exact (c : Cfg Γ Λ σ) (r : Response M)
    (h : PrefixRelation M (c.l,c.var) (fun k i => (c.stk k)[i.val]?) r) :
    r=respond M (c.l,c.var) (stackPrefix M c.stk) := by
  obtain ⟨p,hp,hr⟩ := h
  have he : p=stackPrefix M c.stk := by
    funext k
    apply BoundedList.cells_injective
    funext i
    have hh := congrFun (hp k) i
    simpa only [BoundedList.cells,stackPrefix,List.getElem?_take,ite_eq_left i.isLt] using hh
  rwa [he] at hr
lemma prefixRelation_complete (c : Cfg Γ Λ σ) :
    PrefixRelation M (c.l,c.var) (fun k i => (c.stk k)[i.val]?)
      (respond M (c.l,c.var) (stackPrefix M c.stk)) := by
  refine ⟨stackPrefix M c.stk,?_,rfl⟩
  intro k
  funext i
  simp only [BoundedList.cells,stackPrefix,List.getElem?_take,ite_eq_left i.isLt]

noncomputable def category (i : ℕ) : Fin (2*radius M+1) := ⟨min i (2*radius M),by omega⟩
def cellTable (k : K) (cat : Fin (2*radius M+1))
    (p : BoundedList (Γ k) (2*radius M)) (window : Fin (2*radius M+1) → Option (Γ k)) : Option (Γ k) :=
  if cat.val<p.val.length then p.val[cat.val]? else window ⟨p.val.length,by have := p.property; omega⟩
lemma cellTable_exact (c : Cfg Γ Λ σ) (k : K) (i : ℕ) :
    cellTable M k (category M i) ((respond M (c.l,c.var) (stackPrefix M c.stk)).2 k)
      (fun h => (c.stk k)[(i+radius M)-h.val]?) = ((advance M c).stk k)[i]? := by
  rw [response_cell]
  dsimp only [cellTable,category]
  let p := (respond M (c.l,c.var) (stackPrefix M c.stk)).2 k
  change (if min i (2*radius M)<p.val.length then p.val[min i (2*radius M)]?
    else (c.stk k)[i+radius M-p.val.length]?) =
    if i<p.val.length then p.val[i]? else (c.stk k)[radius M+(i-p.val.length)]?
  have hp := p.property
  by_cases hi : i<p.val.length
  · have hb : i≤2*radius M := by omega
    simp only [min_eq_left hb,ite_eq_left hi]
  · have hb : ¬ min i (2*radius M)<p.val.length := by omega
    simp only [ite_eq_right hi,ite_eq_right hb]
    congr 1
    omega

def clampedCell {Alphabet : Type} (L : ℕ) (row : Row Alphabet L) (j : ℕ) : Option Alphabet :=
  row ⟨min j L,by omega⟩
omit [DecidableEq K] [Fintype Λ] in
lemma clampedCell_eq {Alphabet : Type} (L : ℕ) (row : Row Alphabet L) (h : ValidRow L row) (j : ℕ) :
    clampedCell L row j=rowCell L row j := by
  unfold clampedCell rowCell
  by_cases hj : j≤L
  · simp only [min_eq_left hj,dite_eq_left hj]
  · simp only [min_eq_right (by omega : L≤j),dite_eq_right hj]
    exact h.1

lemma local_transition_exact (L : ℕ) (c d : Cfg Γ Λ σ)
    (hd : ∀ k, (d.stk k).length≤L) (r : Response M)
    (hresp : PrefixRelation M (c.l,c.var) (fun k i => (c.stk k)[i.val]?) r)
    (hctrl : (d.l,d.var)=r.1)
    (hcell : ∀ k i, i≤L → (d.stk k)[i]?=
      cellTable M k (category M i) (r.2 k) (fun h => (c.stk k)[i+radius M-h.val]?)) :
    d=advance M c := by
  have hr := prefixRelation_exact M c r hresp
  have hct : (d.l,d.var)=((advance M c).l,(advance M c).var) :=
    hctrl.trans ((congrArg Prod.fst hr).trans (response_control M c).symm)
  have hs : d.stk=(advance M c).stk := by
    funext k
    apply (stack_eq_of_cells L ((advance M c).stk k) (d.stk k) (hd k) _).symm
    intro i hi
    rw [hcell k i hi,hr,cellTable_exact]
  have hl := congrArg Prod.fst hct
  have hv := congrArg Prod.snd hct
  cases d
  generalize advance M c = e at hl hv hs ⊢
  cases e
  simp only [Cfg.mk.injEq]
  exact ⟨hl,hv,hs⟩
end MetricKMedian.PCP.Tableau

end Inline_PCPTableauLocal

end OAI
