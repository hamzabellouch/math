import Mathlib
import OAI.RepresentationTheory.PartialPermutation.DiagramCounts

namespace OAI

section
namespace PartialPermutation
namespace DiagramCounting
noncomputable section
open Finset

lemma shift_injective : Function.Injective (fun x : ℕ × ℕ => (x.1+1,x.2)) := by
  rintro ⟨i,j⟩ ⟨k,l⟩ h
  simp only [Prod.mk.injEq] at h
  exact Prod.ext (Nat.add_right_cancel h.1) h.2

def dropTop (μ : YoungDiagram) : YoungDiagram where
  cells := μ.cells.preimage (fun x : ℕ × ℕ => (x.1+1,x.2)) shift_injective.injOn
  isLowerSet := by
    intro y x hxy hy
    simp only [Finset.mem_coe,Finset.mem_preimage] at hy ⊢
    have hh : (x.1+1,x.2) ≤ (y.1+1,y.2) := ⟨Nat.add_le_add_right hxy.1 1,hxy.2⟩
    exact μ.isLowerSet hh hy

lemma mem_dropTop (μ : YoungDiagram) (i j : ℕ) :
    (i,j) ∈ dropTop μ ↔ (i+1,j) ∈ μ := by
  change (i,j) ∈ μ.cells.preimage (fun x : ℕ × ℕ => (x.1+1,x.2)) shift_injective.injOn ↔ _
  exact Finset.mem_preimage

def lowerEquiv (μ : YoungDiagram) : (dropTop μ).cells ≃ {x : μ.cells // x.1.1≠0} where
  toFun x := ⟨⟨(x.1.1+1,x.1.2), (mem_dropTop μ _ _).mp x.2⟩,Nat.succ_ne_zero _⟩
  invFun x := ⟨(x.1.1.1-1,x.1.1.2), by
    apply (mem_dropTop μ _ _).mpr
    have he : x.1.1.1-1+1=x.1.1.1 := by have h:=x.2; omega
    rw [he]; exact x.1.2⟩
  left_inv x := by apply Subtype.ext; simp
  right_inv x := by
    apply Subtype.ext; apply Subtype.ext; apply Prod.ext
    · have h:=x.2; dsimp; omega
    · rfl

def rowEquiv (μ : YoungDiagram) : {x : μ.cells // x.1.1=0} ≃ Fin (μ.rowLen 0) where
  toFun x := ⟨x.1.1.2, by have h:=μ.mem_iff_lt_rowLen.mp x.1.2; simpa [x.2] using h⟩
  invFun i := ⟨⟨(0,i), μ.mem_iff_lt_rowLen.mpr i.2⟩,rfl⟩
  left_inv x := by apply Subtype.ext; apply Subtype.ext; exact Prod.ext x.2.symm rfl
  right_inv _ := rfl

lemma dropTop_card (μ : YoungDiagram) :
    (dropTop μ).cells.card = μ.cells.card-μ.rowLen 0 := by
  have h := Fintype.card_congr (lowerEquiv μ)
  rw [Fintype.card_subtype_compl] at h
  have he := Fintype.card_congr (rowEquiv μ)
  simpa only [Fintype.card_coe,Fintype.card_fin,he] using h

lemma eq_of_dropTop_row (μ ν : YoungDiagram) (hd : dropTop μ=dropTop ν)
    (hr : μ.rowLen 0=ν.rowLen 0) : μ=ν := by
  apply YoungDiagram.ext
  apply Finset.ext
  rintro ⟨i,j⟩
  cases i with
  | zero => exact μ.mem_iff_lt_rowLen.trans (hr ▸ ν.mem_iff_lt_rowLen.symm)
  | succ i =>
    change (i+1,j) ∈ μ ↔ (i+1,j) ∈ ν
    rw [← mem_dropTop μ, ← mem_dropTop ν,hd]

lemma transpose_card (μ : YoungDiagram) : μ.transpose.cells.card=μ.cells.card := by
  have e : μ.cells ≃ μ.transpose.cells := {
    toFun := fun x => ⟨x.1.swap, by simpa only [YoungDiagram.mem_cells,
      YoungDiagram.mem_transpose,Prod.swap_swap] using x.2⟩
    invFun := fun x => ⟨x.1.swap,YoungDiagram.mem_transpose.mp x.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  simpa only [Fintype.card_coe] using (Fintype.card_congr e).symm

def ShapeDeficit (n k : ℕ) :=
  {μ : Shape n // μ.1.cells.card-max (μ.1.rowLen 0) (μ.1.colLen 0)=k}

instance (n k : ℕ) : Fintype (ShapeDeficit n k) := by
  classical
  unfold ShapeDeficit
  infer_instance

def deficitCode (n k : ℕ) (μ : ShapeDeficit n k) : Bool × Shape k :=
  if h : μ.1.1.colLen 0 ≤ μ.1.1.rowLen 0 then
    (true,⟨dropTop μ.1.1, by rw [dropTop_card]; simpa only [max_eq_left h] using μ.2⟩)
  else
    (false,⟨dropTop μ.1.1.transpose, by
      rw [dropTop_card,transpose_card,YoungDiagram.rowLen_transpose]
      simpa only [max_eq_right (le_of_not_ge h)] using μ.2⟩)

lemma deficitCode_injective (n k : ℕ) : Function.Injective (deficitCode n k) := by
  intro μ ν he
  unfold deficitCode at he
  split_ifs at he with hμ hν hν
  · have hd : dropTop μ.1.1=dropTop ν.1.1 := congrArg (fun t : Bool × Shape k => t.2.1) he
    have hcμ := μ.2
    have hcν := ν.2
    rw [μ.1.2,max_eq_left hμ] at hcμ
    rw [ν.1.2,max_eq_left hν] at hcν
    have hleμ := rowLen_le_card μ.1.1 0
    have hleν := rowLen_le_card ν.1.1 0
    rw [μ.1.2] at hleμ
    rw [ν.1.2] at hleν
    apply Subtype.ext; apply Subtype.ext
    exact eq_of_dropTop_row _ _ hd (by omega)
  · have hh := congrArg Prod.fst he; cases hh
  · have hh := congrArg Prod.fst he; cases hh
  · have hd : dropTop μ.1.1.transpose=dropTop ν.1.1.transpose :=
      congrArg (fun t : Bool × Shape k => t.2.1) he
    have hcμ := μ.2
    have hcν := ν.2
    rw [μ.1.2,max_eq_right (le_of_not_ge hμ)] at hcμ
    rw [ν.1.2,max_eq_right (le_of_not_ge hν)] at hcν
    have hleμ := colLen_le_card μ.1.1 0
    have hleν := colLen_le_card ν.1.1 0
    rw [μ.1.2] at hleμ
    rw [ν.1.2] at hleν
    have htr := eq_of_dropTop_row _ _ hd (by
      simp only [YoungDiagram.rowLen_transpose]; omega)
    apply Subtype.ext; apply Subtype.ext
    have hh := congrArg YoungDiagram.transpose htr
    simpa only [YoungDiagram.transpose_transpose] using hh

lemma deficit_count_le (n k : ℕ) : Fintype.card (ShapeDeficit n k) ≤ 2*partitionCount k := by
  simpa only [Fintype.card_prod,Fintype.card_bool,partitionCount] using
    Fintype.card_le_of_injective (deficitCode n k) (deficitCode_injective n k)

end
end DiagramCounting
end PartialPermutation
end

end OAI
