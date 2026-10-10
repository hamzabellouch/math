import Mathlib
import OAI.RepresentationTheory.PartialPermutation.FillingExtensions
import OAI.RepresentationTheory.PartialPermutation.Interleavings

namespace OAI

section
namespace PartialPermutation
namespace Tableau
noncomputable section
open Finset

def topPrefix (μ : YoungDiagram) (c : ℕ) (x : μ.cells) : Prop :=
  x.1.1=0 ∧ x.1.2<c

instance (μ : YoungDiagram) (c : ℕ) : DecidablePred (topPrefix μ c) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _))

lemma topPrefix_lower (μ : YoungDiagram) (c : ℕ) :
    IsLowerSet {x | topPrefix μ c x} := by
  intro x y hxy hy
  exact ⟨Nat.eq_zero_of_le_zero (hxy.1.trans_eq hy.1), hxy.2.trans_lt hy.2⟩

def topPrefixEquiv (μ : YoungDiagram) (c : ℕ) (hc : c ≤ μ.rowLen 0) :
    {x // topPrefix μ c x} ≃ Fin c where
  toFun x := ⟨x.1.1.2,x.2.2⟩
  invFun i := ⟨⟨(0,i), μ.mem_iff_lt_rowLen.mpr (i.2.trans_le hc)⟩,rfl,i.2⟩
  left_inv x := by apply Subtype.ext; apply Subtype.ext; exact Prod.ext x.2.1.symm rfl
  right_inv _ := rfl

lemma topPrefix_card (μ : YoungDiagram) (c : ℕ) (hc : c ≤ μ.rowLen 0) :
    Fintype.card {x // topPrefix μ c x} = c := by
  simpa using Fintype.card_congr (topPrefixEquiv μ c hc)

def topRowEquiv (μ : YoungDiagram) : {x : μ.cells // x.1.1=0} ≃ Fin (μ.rowLen 0) where
  toFun x := ⟨x.1.1.2, by have h:=μ.mem_iff_lt_rowLen.mp x.1.2; simpa [x.2] using h⟩
  invFun i := ⟨⟨(0,i), μ.mem_iff_lt_rowLen.mpr i.2⟩,rfl⟩
  left_inv x := by apply Subtype.ext; apply Subtype.ext; exact Prod.ext x.2.symm rfl
  right_inv _ := rfl

lemma lower_card (μ : YoungDiagram) :
    Fintype.card {x : μ.cells // x.1.1 ≠ 0} = μ.cells.card - μ.rowLen 0 := by
  rw [Fintype.card_subtype_compl]
  have h := Fintype.card_congr (topRowEquiv μ)
  rw [Fintype.card_fin] at h
  rw [h, Fintype.card_coe]

lemma topRow_le_card (μ : YoungDiagram) : μ.rowLen 0 ≤ μ.cells.card := by
  have h := Fintype.card_le_of_injective (topRowEquiv μ).symm
    (topRowEquiv μ).symm.injective
  have h' := Fintype.card_subtype_le (fun x : μ.cells => x.1.1=0)
  simpa only [Fintype.card_fin, Fintype.card_coe] using h.trans h'

lemma prefix_upper_card (μ : YoungDiagram) (c : ℕ) (hc : c ≤ μ.rowLen 0) :
    Fintype.card {x // ¬topPrefix μ c x} = μ.cells.card-c := by
  rw [Fintype.card_subtype_compl, topPrefix_card μ c hc, Fintype.card_coe]

def lowerInUpperEquiv (μ : YoungDiagram) (c : ℕ) :
    {x : {x // ¬topPrefix μ c x} // x.1.1.1 ≠ 0} ≃ {x : μ.cells // x.1.1 ≠ 0} where
  toFun x := ⟨x.1.1,x.2⟩
  invFun x := ⟨⟨x.1,fun h => x.2 h.1⟩,x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma row_interleaving_lower_bound (μ : YoungDiagram) :
    (μ.cells.card-μ.rowLen 1).choose (μ.cells.card-μ.rowLen 0) ≤ standardCount μ := by
  let P := topPrefix μ (μ.rowLen 1)
  let Q : {x // ¬P x} → Prop := fun x => x.1.1.1 ≠ 0
  have hP := topPrefix_lower μ (μ.rowLen 1)
  have hQ : ∀ a b : {x // ¬P x}, a < b → (Q a ↔ Q b) := by
    intro a b hab
    change (a.1.1.1 ≠ 0 ↔ b.1.1.1 ≠ 0)
    have hi := hab.le.1
    have hj := hab.le.2
    constructor
    · intro ha hb
      exact ha (Nat.eq_zero_of_le_zero (hi.trans_eq hb))
    · intro hb ha
      have hcol : b.1.1.2 < μ.rowLen 1 :=
        (μ.mem_iff_lt_rowLen.mp b.1.2).trans_le (μ.rowLen_anti 1 b.1.1.1 (by omega))
      exact a.2 ⟨ha,hj.trans_lt hcol⟩
  have h := interleaving_binomial_lower_bound Q hQ
  have hc : μ.rowLen 1 ≤ μ.rowLen 0 := μ.rowLen_anti 0 1 (by omega)
  have hcard : Fintype.card {x : {x // ¬P x} // Q x} = μ.cells.card-μ.rowLen 0 :=
    (Fintype.card_congr (lowerInUpperEquiv μ (μ.rowLen 1))).trans (lower_card μ)
  rw [hcard] at h
  have hu : Fintype.card {x // ¬P x} = μ.cells.card-μ.rowLen 1 := prefix_upper_card μ _ hc
  rw [hu] at h
  exact h.trans (filling_count_mono_complement P hP)

lemma secondRow_le_lower (μ : YoungDiagram) : μ.rowLen 1 ≤ μ.cells.card-μ.rowLen 0 := by
  let f : Fin (μ.rowLen 1) → {x : μ.cells // x.1.1 ≠ 0} := fun i =>
    ⟨⟨(1,i), μ.mem_iff_lt_rowLen.mpr i.2⟩,Nat.one_ne_zero⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    exact congrArg (fun x : {x : μ.cells // x.1.1 ≠ 0} => x.1.1.2) hij
  have h := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_fin, lower_card] using h

end
end Tableau
end PartialPermutation
end

end OAI
