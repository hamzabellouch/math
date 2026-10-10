import Mathlib
import OAI.RepresentationTheory.PartialPermutation.TableauVectors

namespace OAI

section
namespace PartialPermutation.YoungTabloid
noncomputable section
open Finset
open scoped Classical

def rowMoment (μ : YoungDiagram) : ℕ := ∑ x, row μ x

def CrossTransversal (μ : YoungDiagram) (r : μ.cells → ℕ) : Prop :=
  ∀ x y, col μ x=col μ y → r x=r y → x=y

def crossSortedColumn (μ : YoungDiagram) (r : μ.cells → ℕ)
    (hr : CrossTransversal μ r) (j : ℕ) : Col μ j ≃ Fin (μ.colLen j) :=
  (exists_sortingEquiv (Col μ j) (fun x => r x.1)
    (fun x y h => Subtype.ext (hr x.1 y.1 (x.2.trans y.2.symm) h))
    _ (col_card μ j)).choose

lemma crossSortedColumn_mono (μ : YoungDiagram) (r : μ.cells → ℕ)
    (hr : CrossTransversal μ r) (j : ℕ) :
    StrictMono (fun i => r ((crossSortedColumn μ r hr j).symm i).1) :=
  (exists_sortingEquiv (Col μ j) (fun x => r x.1)
    (fun x y h => Subtype.ext (hr x.1 y.1 (x.2.trans y.2.symm) h))
    _ (col_card μ j)).choose_spec

def crossSorting (μ : YoungDiagram) (r : μ.cells → ℕ) (hr : CrossTransversal μ r) :
    Equiv.Perm μ.cells := fiberPermutation (col μ)
      (fun j => (crossSortedColumn μ r hr j).trans (columnEquiv μ j).symm)

lemma crossSorting_row (μ : YoungDiagram) (r : μ.cells → ℕ)
    (hr : CrossTransversal μ r) (x : μ.cells) : row μ (crossSorting μ r hr x) ≤ r x := by
  let e := crossSortedColumn μ r hr (col μ x)
  have h := strictMono_fin_nat_le _ (crossSortedColumn_mono μ r hr (col μ x)) (e ⟨x,rfl⟩)
  change (e ⟨x,rfl⟩).val ≤ r (e.symm (e ⟨x,rfl⟩)).val at h
  erw [Equiv.symm_apply_apply] at h
  exact h

lemma cross_rowMoment_le (μ ν : YoungDiagram) (e : μ.cells ≃ ν.cells) (r : Tabloid ν)
    (hr : CrossTransversal μ (fun x => r.1 (e x))) : rowMoment μ ≤ rowMoment ν := by
  calc
    rowMoment μ = ∑ x, row μ (crossSorting μ _ hr x) :=
      (Equiv.sum_comp (crossSorting μ _ hr) (row μ)).symm
    _ ≤ ∑ x, r.1 (e x) := Finset.sum_le_sum (fun x _ => crossSorting_row μ _ hr x)
    _ = ∑ x, r.1 x := Equiv.sum_comp e r.1
    _ = rowMoment ν := rowSum ν r

def rowFiberEquiv (μ : YoungDiagram) (i : ℕ) : {x : μ.cells // row μ x=i} ≃ Fin (μ.rowLen i) where
  toFun x := ⟨col μ x.1,by
    have h := μ.mem_iff_lt_rowLen.mp x.1.2
    have hi : x.1.1.1=i := x.2
    simpa only [col,hi] using h⟩
  invFun j := ⟨rowCell μ i j,rfl⟩
  left_inv x := by apply Subtype.ext; apply Subtype.ext; exact Prod.ext x.2.symm rfl
  right_inv _ := rfl

lemma shape_eq_of_row_equiv (μ ν : YoungDiagram) (e : μ.cells ≃ ν.cells)
    (h : ∀ x, row ν (e x)=row μ x) : μ=ν := by
  have hr (i : ℕ) : μ.rowLen i=ν.rowLen i := by
    let er : {x : μ.cells // row μ x=i} ≃ {x : ν.cells // row ν x=i} :=
      e.subtypeEquiv (fun x => by rw [h])
    simpa only [Fintype.card_fin] using (Fintype.card_congr (rowFiberEquiv μ i)).symm.trans
      ((Fintype.card_congr er).trans (Fintype.card_congr (rowFiberEquiv ν i)))
  apply YoungDiagram.ext
  ext x
  exact (μ.mem_iff_lt_rowLen).trans ((hr x.1) ▸ ν.mem_iff_lt_rowLen.symm)

lemma cross_equal_moment_shape_eq (μ ν : YoungDiagram) (e : μ.cells ≃ ν.cells)
    (r : Tabloid ν) (hr : CrossTransversal μ (fun x => r.1 (e x)))
    (hm : rowMoment μ=rowMoment ν) : μ=ν := by
  let p := crossSorting μ _ hr
  have hs : (∑ x, row μ (p x))=∑ x, r.1 (e x) := by
    rw [Equiv.sum_comp p,Equiv.sum_comp e,rowSum]
    exact hm
  have he : ∀ x, row μ (p x)=r.1 (e x) :=
    fun x => (Finset.sum_eq_sum_iff_of_le (fun x _ => crossSorting_row μ _ hr x)).mp hs x (mem_univ x)
  obtain ⟨q,hq⟩ := r.2
  apply shape_eq_of_row_equiv μ ν ((p.symm.trans e).trans q)
  intro x
  simpa [hq] using (he (p.symm x)).symm

end
end PartialPermutation.YoungTabloid
end

end OAI
