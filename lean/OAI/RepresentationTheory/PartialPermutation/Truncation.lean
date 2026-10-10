import Mathlib
import OAI.RepresentationTheory.PartialPermutation.RowBounds

namespace OAI

section
namespace PartialPermutation
namespace Tableau
noncomputable section
open Finset

def truncateLower (μ : YoungDiagram)
    (T : StandardFilling {x : μ.cells // x.1.1 ≠ 0}) (b : ℕ) : YoungDiagram := by
  classical
  let P : ℕ × ℕ → Prop := fun x => ∃ hx : x ∈ μ.cells,
    ∀ hn : x.1 ≠ 0, (T.1 ⟨⟨x,hx⟩,hn⟩).val < b
  refine ⟨μ.cells.filter P, ?_⟩
  intro y x hxy hy
  obtain ⟨hy,hpy⟩ := Finset.mem_filter.mp hy
  obtain ⟨_,hty⟩ := hpy
  have hx := μ.isLowerSet hxy hy
  apply Finset.mem_filter.mpr
  refine ⟨hx,hx,?_⟩
  intro hn
  have hny : y.1≠0 := by intro he; exact hn (Nat.eq_zero_of_le_zero (hxy.1.trans_eq he))
  have hmono : (T.1 ⟨⟨x,hx⟩,hn⟩).val ≤ (T.1 ⟨⟨y,hy⟩,hny⟩).val :=
    T.2.monotone (show (⟨⟨x,hx⟩,hn⟩ : {x : μ.cells // x.1.1≠0}) ≤
      ⟨⟨y,hy⟩,hny⟩ from hxy)
  exact hmono.trans_lt (hty hny)

lemma mem_truncateLower (μ : YoungDiagram)
    (T : StandardFilling {x : μ.cells // x.1.1 ≠ 0}) (b : ℕ) (x : ℕ × ℕ) :
    x ∈ (truncateLower μ T b).cells ↔ ∃ hx : x ∈ μ.cells,
      ∀ hn : x.1 ≠ 0, (T.1 ⟨⟨x,hx⟩,hn⟩).val < b := by
  classical
  simp only [truncateLower, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨h.choose,h⟩⟩

lemma truncateLower_le (μ : YoungDiagram)
    (T : StandardFilling {x : μ.cells // x.1.1 ≠ 0}) (b : ℕ) :
    truncateLower μ T b ≤ μ := by
  intro x hx
  exact (mem_truncateLower μ T b x).mp hx |>.choose

lemma truncateLower_topRow (μ : YoungDiagram)
    (T : StandardFilling {x : μ.cells // x.1.1 ≠ 0}) (b : ℕ) :
    (truncateLower μ T b).rowLen 0 = μ.rowLen 0 := by
  have hm : ∀ j, (0,j) ∈ truncateLower μ T b ↔ (0,j) ∈ μ := by
    intro j
    rw [← YoungDiagram.mem_cells, mem_truncateLower]
    exact ⟨fun h => h.choose, fun h => ⟨h,fun hn => (hn rfl).elim⟩⟩
  apply le_antisymm
  · by_contra h
    have hh := (hm (μ.rowLen 0)).mp ((truncateLower μ T b).mem_iff_lt_rowLen.mpr (by omega))
    exact (lt_irrefl _) (μ.mem_iff_lt_rowLen.mp hh)
  · by_contra h
    have hh := (hm ((truncateLower μ T b).rowLen 0)).mpr (μ.mem_iff_lt_rowLen.mpr (by omega))
    exact (lt_irrefl _) ((truncateLower μ T b).mem_iff_lt_rowLen.mp hh)

def truncatedLowerEquiv (μ : YoungDiagram)
    (T : StandardFilling {x : μ.cells // x.1.1 ≠ 0}) (b : ℕ)
    (hb : b ≤ μ.cells.card - μ.rowLen 0) :
    {x : (truncateLower μ T b).cells // x.1.1 ≠ 0} ≃ Fin b := by
  let incl : {x : (truncateLower μ T b).cells // x.1.1 ≠ 0} →
      {x : μ.cells // x.1.1 ≠ 0} := fun x =>
    ⟨⟨x.1.1,truncateLower_le μ T b x.1.2⟩,x.2⟩
  have hb' : b ≤ Fintype.card {x : μ.cells // x.1.1≠0} := by rwa [lower_card]
  let val : Fin b → {x : μ.cells // x.1.1 ≠ 0} := fun i =>
    T.1.symm ⟨i.val,i.isLt.trans_le hb'⟩
  have hv : ∀ i, (val i).1.1 ∈ (truncateLower μ T b).cells := by
    intro i
    apply (mem_truncateLower μ T b _).mpr
    refine ⟨(val i).1.2,?_⟩
    intro hn
    have he : (⟨⟨(val i).1.1,(val i).1.2⟩,hn⟩ : {x : μ.cells // x.1.1 ≠ 0}) = val i := rfl
    rw [he]
    simp [val]
  have ht : ∀ x, (T.1 (incl x)).val < b := by
    intro x
    exact ((mem_truncateLower μ T b x.1.1).mp x.1.2).choose_spec x.2
  refine {toFun := fun x => ⟨T.1 (incl x), ht x⟩
          invFun := fun i => ⟨⟨(val i).1.1,hv i⟩,(val i).2⟩
          left_inv := ?_
          right_inv := ?_}
  · intro x
    apply Subtype.ext
    apply Subtype.ext
    have he : val ⟨T.1 (incl x), ht x⟩ = incl x := by simp [val]
    exact congrArg (fun y : {x : μ.cells // x.1.1≠0} => y.1.1) he
  · intro i
    apply Fin.ext
    change (T.1 (val i)).val = i.val
    simp [val]

lemma truncateLower_card (μ : YoungDiagram)
    (T : StandardFilling {x : μ.cells // x.1.1 ≠ 0}) (b : ℕ)
    (hb : b ≤ μ.cells.card - μ.rowLen 0) :
    (truncateLower μ T b).cells.card = μ.rowLen 0 + b := by
  have h := Fintype.card_congr (truncatedLowerEquiv μ T b hb)
  rw [Fintype.card_fin, lower_card, truncateLower_topRow] at h
  have hle := topRow_le_card (truncateLower μ T b)
  rw [truncateLower_topRow] at hle
  omega

lemma binomial_lower_bound (μ : YoungDiagram) (b : ℕ)
    (hb : b ≤ min (μ.rowLen 0) (μ.cells.card-μ.rowLen 0)) :
    (μ.rowLen 0).choose b ≤ standardCount μ := by
  let T := chosenFilling {x : μ.cells // x.1.1≠0}
  let ν := truncateLower μ T b
  have hb' := hb.trans (min_le_right _ _)
  have htop : ν.rowLen 0 = μ.rowLen 0 := truncateLower_topRow μ T b
  have hcard : ν.cells.card = μ.rowLen 0 + b := truncateLower_card μ T b hb'
  have hsecond := secondRow_le_lower ν
  rw [htop,hcard,Nat.add_sub_cancel_left] at hsecond
  have h := row_interleaving_lower_bound ν
  rw [htop,hcard,Nat.add_sub_cancel_left] at h
  exact ((Nat.choose_le_choose b (show μ.rowLen 0 ≤ μ.rowLen 0+b-ν.rowLen 1 by omega)).trans h).trans
    (standardCount_mono (truncateLower_le μ T b))

end
end Tableau
end PartialPermutation
end

end OAI
