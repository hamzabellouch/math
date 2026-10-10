import Mathlib

namespace OAI

section
namespace PartialPermutation
namespace DiagramCounting
noncomputable section
open Finset

lemma rectangle_card_le (μ : YoungDiagram) (i j : ℕ) (h : (i,j) ∈ μ) :
    (i+1)*(j+1) ≤ μ.cells.card := by
  have hs : (Finset.range (i+1)) ×ˢ (Finset.range (j+1)) ⊆ μ.cells := by
    intro x hx
    rcases Finset.mem_product.mp hx with ⟨hx,hy⟩
    exact μ.isLowerSet ⟨by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hx,
      by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hy⟩ h
  simpa only [Finset.card_product, Finset.card_range] using Finset.card_le_card hs

lemma cell_bounded (μ : YoungDiagram) (x : μ.cells) :
    x.1.1 < μ.cells.card ∧ x.1.2 < μ.cells.card := by
  have h := rectangle_card_le μ x.1.1 x.1.2 x.2
  constructor <;> nlinarith

lemma rowLen_le_card (μ : YoungDiagram) (i : ℕ) : μ.rowLen i ≤ μ.cells.card := by
  by_contra h
  have hx := (μ.mem_iff_lt_rowLen.mpr (show μ.cells.card < μ.rowLen i by omega))
  have hh := cell_bounded μ ⟨(i,μ.cells.card),hx⟩
  exact (lt_irrefl _) hh.2

lemma colLen_le_card (μ : YoungDiagram) (j : ℕ) : μ.colLen j ≤ μ.cells.card := by
  by_contra h
  have hx := (μ.mem_iff_lt_colLen.mpr (show μ.cells.card < μ.colLen j by omega))
  have hh := cell_bounded μ ⟨(μ.cells.card,j),hx⟩
  exact (lt_irrefl _) hh.1

def Shape (n : ℕ) := {μ : YoungDiagram // μ.cells.card=n}

def boxCode (n : ℕ) (μ : Shape n) :
    ((Finset.range n) ×ˢ (Finset.range n)).powerset := by
  refine ⟨μ.1.cells,Finset.mem_powerset.mpr ?_⟩
  intro x hx
  have hh := cell_bounded μ.1 ⟨x,hx⟩
  rw [μ.2] at hh
  simpa only [Finset.mem_product, Finset.mem_range] using hh

lemma boxCode_injective (n : ℕ) : Function.Injective (boxCode n) := by
  intro μ ν h
  apply Subtype.ext
  apply YoungDiagram.ext
  exact congrArg Subtype.val h

instance (n : ℕ) : Fintype (Shape n) := Fintype.ofInjective (boxCode n) (boxCode_injective n)

def partitionCount (n : ℕ) := Fintype.card (Shape n)

def shortCode (n m : ℕ) (μ : Shape n) :
    (Fin m → Fin (n+1)) × (Fin m → Fin (n+1)) :=
  (fun i => ⟨μ.1.rowLen i, by have h:=rowLen_le_card μ.1 i; rw [μ.2] at h; omega⟩,
   fun j => ⟨μ.1.colLen j, by have h:=colLen_le_card μ.1 j; rw [μ.2] at h; omega⟩)

lemma no_large_corner (n m : ℕ) (hn : n < (m+1)*(m+1)) (μ : Shape n)
    {i j : ℕ} (h : (i,j) ∈ μ.1) : i < m ∨ j < m := by
  by_contra hh
  push Not at hh
  have hcorner : (m,m) ∈ μ.1 := μ.1.isLowerSet hh h
  have hc := rectangle_card_le μ.1 m m hcorner
  rw [μ.2] at hc
  omega

lemma shortCode_injective (n m : ℕ) (hn : n < (m+1)*(m+1)) :
    Function.Injective (shortCode n m) := by
  intro μ ν he
  have hr : ∀ i : Fin m, μ.1.rowLen i = ν.1.rowLen i := by
    intro i
    exact congrArg (fun z : (Fin m → Fin (n+1)) × (Fin m → Fin (n+1)) => (z.1 i).val) he
  have hc : ∀ j : Fin m, μ.1.colLen j = ν.1.colLen j := by
    intro j
    exact congrArg (fun z : (Fin m → Fin (n+1)) × (Fin m → Fin (n+1)) => (z.2 j).val) he
  apply Subtype.ext
  apply YoungDiagram.ext
  apply Finset.ext
  rintro ⟨i,j⟩
  constructor
  · intro h
    rcases no_large_corner n m hn μ h with hi | hj
    · apply ν.1.mem_iff_lt_rowLen.mpr
      rw [← hr ⟨i,hi⟩]
      exact μ.1.mem_iff_lt_rowLen.mp h
    · apply ν.1.mem_iff_lt_colLen.mpr
      rw [← hc ⟨j,hj⟩]
      exact μ.1.mem_iff_lt_colLen.mp h
  · intro h
    rcases no_large_corner n m hn ν h with hi | hj
    · apply μ.1.mem_iff_lt_rowLen.mpr
      rw [hr ⟨i,hi⟩]
      exact ν.1.mem_iff_lt_rowLen.mp h
    · apply μ.1.mem_iff_lt_colLen.mpr
      rw [hc ⟨j,hj⟩]
      exact ν.1.mem_iff_lt_colLen.mp h

lemma partitionCount_le_shortCode (n m : ℕ) (hn : n < (m+1)*(m+1)) :
    partitionCount n ≤ (n+1)^(2*m) := by
  have h := Fintype.card_le_of_injective (shortCode n m) (shortCode_injective n m hn)
  simpa only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, ← pow_add,
    ← two_mul, partitionCount] using h

lemma partitionCount_le_sqrt (n : ℕ) : partitionCount n ≤ (n+1)^(2*n.sqrt) :=
  partitionCount_le_shortCode n n.sqrt (Nat.lt_succ_sqrt n)

end
end DiagramCounting
end PartialPermutation
end

end OAI
