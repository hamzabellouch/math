import Mathlib
import OAI.RepresentationTheory.PartialPermutation.ColumnSorting

namespace OAI

section
namespace PartialPermutation.YoungTabloid
noncomputable section
open Finset
open scoped Classical

lemma cell_eq_of_row_col (μ : YoungDiagram) {x y : μ.cells}
    (hr : row μ x=row μ y) (hc : col μ x=col μ y) : x=y :=
  Subtype.ext (Prod.ext hr hc)

lemma cell_lt_of_column (μ : YoungDiagram) {x y : μ.cells}
    (hc : col μ x=col μ y) (hr : row μ x<row μ y) : x<y := by
  apply lt_of_le_of_ne
  · exact ⟨hr.le,hc.le⟩
  · intro h
    exact hr.ne (congrArg (row μ) h)

def columnRestrict (μ : YoungDiagram) (c : columnGroup μ) (j : ℕ) : Equiv.Perm (Col μ j) where
  toFun x := ⟨c.1 x.1,(c.2 x.1).trans x.2⟩
  invFun x := ⟨c.1⁻¹ x.1,((c⁻¹).2 x.1).trans x.2⟩
  left_inv x := by apply Subtype.ext; exact c.1.symm_apply_apply _
  right_inv x := by apply Subtype.ext; exact c.1.apply_symm_apply _

lemma column_monovary (μ : YoungDiagram) (f : μ.cells → ℕ) (hf : StrictMono f) (j : ℕ) :
    Monovary (fun x : Col μ j => f x.1) (fun x => row μ x.1) := by
  intro x y h
  exact (hf (cell_lt_of_column μ (x.2.trans y.2.symm) h)).le

lemma column_rearrangement (μ : YoungDiagram) (f : μ.cells → ℕ) (hf : StrictMono f)
    (c : columnGroup μ) (j : ℕ) :
    (∑ x : Col μ j, f x.1 * row μ (c.1 x.1)) ≤ ∑ x : Col μ j, f x.1 * row μ x.1 :=
  (column_monovary μ f hf j).sum_mul_comp_perm_le_sum_mul (σ := columnRestrict μ c j)

lemma fin_perm_mono_eq (n : ℕ) (p : Equiv.Perm (Fin n)) (hp : StrictMono p) : p=1 := by
  have hle (i : Fin n) : i.val≤(p i).val := strictMono_fin_nat_le _
    (fun i j h => hp h) i
  have heq : (∑ i : Fin n, i.val)=∑ i : Fin n, (p i).val := (Equiv.sum_comp p Fin.val).symm
  have hh := (Finset.sum_eq_sum_iff_of_le (fun i _ => hle i)).mp heq
  apply Equiv.ext
  intro i
  exact Fin.ext (hh i (mem_univ _)).symm

lemma column_rearrangement_eq (μ : YoungDiagram) (f : μ.cells → ℕ) (hf : StrictMono f)
    (c : columnGroup μ) (j : ℕ)
    (he : (∑ x : Col μ j, f x.1 * row μ (c.1 x.1)) = ∑ x : Col μ j, f x.1 * row μ x.1) :
    ∀ x : Col μ j, c.1 x.1=x.1 := by
  have hm := (column_monovary μ f hf j).sum_mul_comp_perm_eq_sum_mul_iff
    (σ := columnRestrict μ c j) |>.mp he
  let e := columnEquiv μ j
  let p := e.symm.trans ((columnRestrict μ c j).trans e)
  have hp : StrictMono p := by
    intro i k hik
    let x := e.symm i
    let y := e.symm k
    have hxy : f x.1 < f y.1 := hf (cell_lt_of_column μ (x.2.trans y.2.symm) hik)
    change row μ (c.1 x.1) < row μ (c.1 y.1)
    by_contra h
    have hr : row μ (c.1 y.1) < row μ (c.1 x.1) := by
      apply lt_of_le_of_ne (Nat.le_of_not_gt h)
      intro hh
      have heq := c.1.injective (cell_eq_of_row_col μ hh
        ((c.2 y.1).trans ((y.2.trans x.2.symm).trans (c.2 x.1).symm)))
      exact hxy.ne (congrArg f heq.symm)
    exact (not_le_of_gt hxy) (hm hr)
  have hp1 := fin_perm_mono_eq _ p hp
  intro x
  have hx := Equiv.congr_fun hp1 (e x)
  change e (columnRestrict μ c j (e.symm (e x)))=e x at hx
  erw [Equiv.symm_apply_apply] at hx
  exact congrArg Subtype.val (e.injective hx)

def colIndex (μ : YoungDiagram) (x : μ.cells) : Fin (μ.rowLen 0) :=
  ⟨col μ x,(μ.mem_iff_lt_rowLen.mp x.2).trans_le
    (μ.rowLen_anti 0 x.1.1 (Nat.zero_le _))⟩

def columnDecomp (μ : YoungDiagram) : μ.cells ≃ Σ j : Fin (μ.rowLen 0), Col μ j where
  toFun x := ⟨colIndex μ x,⟨x,rfl⟩⟩
  invFun x := x.2.1
  left_inv _ := rfl
  right_inv x := by
    obtain ⟨j,x,hx⟩ := x
    have hj : colIndex μ x=j := Fin.ext hx
    cases hj
    rfl

lemma sum_columns (μ : YoungDiagram) (f : μ.cells → ℕ) :
    (∑ x, f x)=∑ j : Fin (μ.rowLen 0), ∑ x : Col μ j, f x.1 := by
  exact (Fintype.sum_equiv (columnDecomp μ) _
    (fun x : Σ j : Fin (μ.rowLen 0), Col μ j => f x.2.1) (fun _ => rfl)).trans
    (Fintype.sum_sigma _)

lemma full_rearrangement (μ : YoungDiagram) (f : μ.cells → ℕ) (hf : StrictMono f)
    (c : columnGroup μ) :
    (∑ x, f x * row μ (c.1 x)) ≤ ∑ x, f x * row μ x := by
  rw [sum_columns, sum_columns]
  exact Finset.sum_le_sum (fun j _ => column_rearrangement μ f hf c j)

lemma full_rearrangement_eq (μ : YoungDiagram) (f : μ.cells → ℕ) (hf : StrictMono f)
    (c : columnGroup μ) (he : (∑ x, f x * row μ (c.1 x)) = ∑ x, f x * row μ x) : c=1 := by
  rw [sum_columns, sum_columns] at he
  have hh := (Finset.sum_eq_sum_iff_of_le
    (fun (j : Fin (μ.rowLen 0)) _ => column_rearrangement μ f hf c j)).mp he
  apply Subtype.ext
  apply Equiv.ext
  intro x
  exact column_rearrangement_eq μ f hf c (colIndex μ x)
    (hh (colIndex μ x) (mem_univ _)) ⟨x,rfl⟩

end
end PartialPermutation.YoungTabloid
end

end OAI
