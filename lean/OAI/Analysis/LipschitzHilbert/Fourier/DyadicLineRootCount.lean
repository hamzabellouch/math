import OAI.Analysis.LipschitzHilbert.Fourier.DyadicLineCountableTail
import OAI.Analysis.LipschitzHilbert.Fourier.DyadicLineCount

namespace OAI

/-! The count in one grid agrees on a root with the count of its selected descendants. -/

noncomputable section

open Set MeasureTheory Function
open scoped BigOperators ENNReal

namespace LipschitzHilbert.DyadicLineGrid

attribute [local instance] Classical.propDecidable

abbrev GridOccurrence (B : Type*) := B × ℤ × ℤ

def maximalCell {B : Type*} (f : B → ℝ → ℝ) (q top : ℤ) (β : ℝ)
    (a : GridOccurrence B) : Set ℝ :=
  if MaximalBad q top (Bad q (f a.1) β) a.2.1 a.2.2 then cell q a.2.1 a.2.2 else ∅

def gridCount {B : Type*} (f : B → ℝ → ℝ) (q top : ℤ) (β : ℝ) : ℝ → ℝ≥0∞ :=
  occurrenceCount (maximalCell f q top β)

def RootOccurrence {B : Type*} (f : B → ℝ → ℝ) (q top : ℤ) (β : ℝ) (j : ℤ) :=
  {a : GridOccurrence B // MaximalBad q top (Bad q (f a.1) β) a.2.1 a.2.2 ∧
    cell q a.2.1 a.2.2 ⊆ cell q top j}

theorem selectedCount_eq_gridCounts {B X : Type*} (f : B → X × ℝ → ℝ)
    (top : ℤ) (β : ℝ) (p : X × ℝ) :
    selectedCount f top β p =
      gridCount (fun b x => f b (p.1, x)) 0 top β p.2 +
        gridCount (fun b x => f b (p.1, x)) 1 top β p.2 := by
  classical
  unfold selectedCount
  rw [ENNReal.tsum_prod']
  have hterm (q : ℤ) :
      (∑' a : GridOccurrence B, (selectedSet f top β (q, a)).indicator 1 p) =
        if q ∈ ({0, 1} : Finset ℤ) then gridCount (fun b x => f b (p.1, x)) q top β p.2 else 0 := by
    by_cases hq : q ∈ ({0, 1} : Finset ℤ)
    · rw [ite_eq_left hq]
      unfold gridCount occurrenceCount
      apply tsum_congr
      intro a
      by_cases hm : MaximalBad q top (Bad q (fun x => f a.1 (p.1, x)) β) a.2.1 a.2.2
      · simp [selectedSet, maximalCell, hq, hm, indicator_apply]
      · simp [selectedSet, maximalCell, hq, hm]
    · rw [ite_eq_right hq]
      simp [selectedSet, hq]
  simp_rw [hterm]
  rw [tsum_eq_sum (s := ({0, 1} : Finset ℤ)) (fun q hq => by simp [hq])]
  simp

theorem gridCount_eq_rootCount {B : Type*} (f : B → ℝ → ℝ) (q top : ℤ) (β : ℝ)
    (j : ℤ) {x : ℝ} (hx : x ∈ cell q top j) :
    gridCount f q top β x =
      occurrenceCount (fun a : RootOccurrence f q top β j => cell q a.1.2.1 a.1.2.2) x := by
  classical
  let g : GridOccurrence B → ℝ≥0∞ := fun a => (maximalCell f q top β a).indicator 1 x
  have hs : support g ⊆ {a | MaximalBad q top (Bad q (f a.1) β) a.2.1 a.2.2 ∧
      cell q a.2.1 a.2.2 ⊆ cell q top j} := by
    intro a ha
    have ha0 : g a ≠ 0 := ha
    by_cases hm : MaximalBad q top (Bad q (f a.1) β) a.2.1 a.2.2
    · have hax : x ∈ cell q a.2.1 a.2.2 := by
        by_contra hn
        simp only [g, maximalCell, ite_eq_left hm, indicator_of_notMem hn] at ha0
        exact ha0 rfl
      exact ⟨hm, cell_subset_of_intersect hm.1 ⟨x, hax, hx⟩⟩
    · simp only [g, maximalCell, ite_eq_right hm, indicator_empty] at ha0
      exact (ha0 rfl).elim
  have heq := tsum_subtype_eq_of_support_subset hs
  change (∑' a, g a) = _
  rw [← heq]
  apply tsum_congr
  intro a
  simp only [g, maximalCell, ite_eq_left a.property.1]

theorem gridCount_root_tail {B : Type*} [Countable B]
    (f : B → ℝ → ℝ) (q top : ℤ) {β C : ℝ} (hβ : 0 < β) (hC : 0 < C)
    (hf : ∀ b, Measurable (f b)) (hbound : ∀ b x, 0 ≤ f b x ∧ f b x ≤ 1)
    (hsum : ∀ s : Finset B, ∀ x, (∑ b ∈ s, f b x) ≤ C)
    (j : ℤ) {lambda : ℝ} (hlambda : 0 ≤ lambda) :
    volume.real ({x | ENNReal.ofReal lambda < gridCount f q top β x} ∩ cell q top j) ≤
      2 * scale top * Real.exp (-lambda / (2 * (C / β))) := by
  classical
  have : Countable (RootOccurrence f q top β j) := by
    unfold RootOccurrence
    infer_instance
  have ht := maximal_bad_countable_tail (ι := RootOccurrence f q top β j) q top f
    (fun a => a.1.1) (fun a => a.1.2.1) (fun a => a.1.2.2)
    (fun a b hb hl hp => Subtype.ext (Prod.ext hb (Prod.ext hl hp))) hβ hC
    (fun a => a.property.1) hf hbound hsum top j (fun a => a.property.2) hlambda
  convert ht using 2
  ext x
  by_cases hx : x ∈ cell q top j
  · simp only [mem_inter_iff, mem_ofPred_eq, hx, and_true,
      gridCount_eq_rootCount f q top β j hx]
  · simp only [mem_inter_iff, hx, and_false]

end LipschitzHilbert.DyadicLineGrid

end

end OAI
