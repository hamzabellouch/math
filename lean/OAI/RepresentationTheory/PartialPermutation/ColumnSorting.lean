import Mathlib
import OAI.RepresentationTheory.PartialPermutation.Tabloids

namespace OAI

section
namespace PartialPermutation
namespace YoungTabloid
noncomputable section
open Finset
open scoped Classical

lemma exists_sortingEquiv (α : Type*) [Fintype α] (r : α → ℕ) (hr : Function.Injective r)
    (n : ℕ) (hn : Fintype.card α=n) :
    ∃ e : α ≃ Fin n, StrictMono (fun i => r (e.symm i)) := by
  let : LinearOrder α := LinearOrder.lift' r hr
  let e := Fintype.orderIsoFinOfCardEq α hn
  exact ⟨e.toEquiv.symm, e.strictMono⟩

lemma strictMono_fin_nat_le {n : ℕ} (f : Fin n → ℕ) (hf : StrictMono f) (i : Fin n) :
    i.val ≤ f i := by
  obtain ⟨i,hi⟩ := i
  induction i with
  | zero => exact Nat.zero_le _
  | succ i ih =>
    have hi' : i<n := by omega
    have h := hf (show (⟨i,hi'⟩:Fin n)<⟨i+1,hi⟩ by simp)
    have ih' := ih hi'
    change i ≤ f ⟨i,hi'⟩ at ih'
    change i+1 ≤ f ⟨i+1,hi⟩
    omega

def Transversal (μ : YoungDiagram) (r : Tabloid μ) : Prop :=
  ∀ x y : μ.cells, col μ x=col μ y → r.1 x=r.1 y → x=y

lemma transversal_col_injective (μ : YoungDiagram) (r : Tabloid μ) (hr : Transversal μ r)
    (j : ℕ) : Function.Injective (fun x : Col μ j => r.1 x.1) := by
  intro x y h
  apply Subtype.ext
  exact hr x.1 y.1 (x.2.trans y.2.symm) h

def sortedColumn (μ : YoungDiagram) (r : Tabloid μ) (hr : Transversal μ r) (j : ℕ) :
    Col μ j ≃ Fin (μ.colLen j) :=
  (exists_sortingEquiv (Col μ j) (fun x => r.1 x.1)
    (transversal_col_injective μ r hr j) _ (col_card μ j)).choose

lemma sortedColumn_mono (μ : YoungDiagram) (r : Tabloid μ) (hr : Transversal μ r) (j : ℕ) :
    StrictMono (fun i => r.1 ((sortedColumn μ r hr j).symm i).1) :=
  (exists_sortingEquiv (Col μ j) (fun x => r.1 x.1)
    (transversal_col_injective μ r hr j) _ (col_card μ j)).choose_spec

def fiberPermutation {α ι : Type*} (r : α → ι)
    (p : ∀ i, Equiv.Perm {a // r a=i}) : Equiv.Perm α :=
  (Equiv.sigmaFiberEquiv r).symm.trans
    ((Equiv.sigmaCongrRight p).trans (Equiv.sigmaFiberEquiv r))

lemma fiberPermutation_apply {α ι : Type*} (r : α → ι)
    (p : ∀ i, Equiv.Perm {a // r a=i}) (a : α) :
    fiberPermutation r p a = (p (r a) ⟨a,rfl⟩).1 := rfl

lemma fiberPermutation_rank {α ι : Type*} (r : α → ι)
    (p : ∀ i, Equiv.Perm {a // r a=i}) (a : α) :
    r (fiberPermutation r p a)=r a := (p (r a) ⟨a,rfl⟩).2

def columnSorting (μ : YoungDiagram) (r : Tabloid μ) (hr : Transversal μ r) :
    Equiv.Perm μ.cells :=
  fiberPermutation (col μ) (fun j => (sortedColumn μ r hr j).trans (columnEquiv μ j).symm)

lemma columnSorting_mem (μ : YoungDiagram) (r : Tabloid μ) (hr : Transversal μ r) :
    columnSorting μ r hr ∈ columnGroup μ :=
  fiberPermutation_rank (col μ) _

lemma columnSorting_row (μ : YoungDiagram) (r : Tabloid μ) (hr : Transversal μ r)
    (x : μ.cells) : row μ (columnSorting μ r hr x) ≤ r.1 x := by
  let e := sortedColumn μ r hr (col μ x)
  have h := strictMono_fin_nat_le _ (sortedColumn_mono μ r hr (col μ x)) (e ⟨x,rfl⟩)
  change (e ⟨x,rfl⟩).val ≤ r.1 (e.symm (e ⟨x,rfl⟩)).val at h
  erw [Equiv.symm_apply_apply] at h
  exact h

lemma transversal_eq_column (μ : YoungDiagram) (r : Tabloid μ) (hr : Transversal μ r) :
    ∃ c : columnGroup μ, r.1=fun x => row μ (c.1 x) := by
  let c := columnSorting μ r hr
  have hle := columnSorting_row μ r hr
  have heq : (∑ x, row μ (c x))=∑ x, r.1 x := by
    rw [rowSum]
    exact Fintype.sum_equiv c _ _ (fun _ => rfl)
  refine ⟨⟨c,columnSorting_mem μ r hr⟩,funext (fun x => ?_)⟩
  exact (Finset.sum_eq_sum_iff_of_le (fun x _ => hle x)).mp heq x (Finset.mem_univ x) |>.symm

lemma column_row_injective (μ : YoungDiagram) :
    Function.Injective (fun c : columnGroup μ => fun x => row μ (c.1 x)) := by
  intro c d h
  apply Subtype.ext
  apply Equiv.ext
  intro x
  apply Subtype.ext
  exact Prod.ext (congrFun h x) ((c.2 x).trans (d.2 x).symm)

lemma unique_column_of_transversal (μ : YoungDiagram) (r : Tabloid μ) (hr : Transversal μ r) :
    ∃! c : columnGroup μ, r.1=fun x => row μ (c.1 x) := by
  obtain ⟨c,hc⟩ := transversal_eq_column μ r hr
  exact ⟨c,hc,fun d hd => column_row_injective μ (hd.symm.trans hc)⟩

end
end YoungTabloid
end PartialPermutation
end

end OAI
