import OAI.GroupTheory.PolycyclicRecognition.Algebra.BracketWords
import Mathlib.Algebra.Lie.Nilpotent
import Mathlib.Data.Finset.Prod

namespace OAI

/-! # A finite list containing every nonzero bracket word

A word of depth `k` belongs to the `k`th lower central ideal. Thus a
nilpotency bound gives a finite list containing every nonzero evaluated
word. The depth cutoff avoids choosing a minimal nilpotence class.
-/

noncomputable section

namespace PolycyclicRecognition

open LieModule Module

variable {I L : Type*} [LieRing L] [LieAlgebra ℝ L]

def bracketWordDepth : FreeMagma I → ℕ
  | .of _ => 0
  | .mul a b => max (bracketWordDepth a) (bracketWordDepth b) + 1

theorem evalBracketWord_mem_lowerCentralSeries (X : I → L) (w : FreeMagma I) :
    evalBracketWord X w ∈ lowerCentralSeries ℝ L L (bracketWordDepth w) := by
  induction w using FreeMagma.rec with
  | of i => exact LieSubmodule.mem_top _
  | mul a b ha hb =>
    change ⁅evalBracketWord X a, evalBracketWord X b⁆ ∈
      lowerCentralSeries ℝ L L (max (bracketWordDepth a) (bracketWordDepth b) + 1)
    rw [lowerCentralSeries_succ]
    rcases le_total (bracketWordDepth a) (bracketWordDepth b) with hab | hba
    · rw [max_eq_right hab]
      exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top _) hb
    · rw [max_eq_left hba, ← lie_skew]
      have hh : ⁅evalBracketWord X b, evalBracketWord X a⁆ ∈
          ⁅(⊤ : LieIdeal ℝ L), lowerCentralSeries ℝ L L (bracketWordDepth a)⁆ :=
        LieSubmodule.lie_mem_lie (LieSubmodule.mem_top _) ha
      exact (⁅(⊤ : LieIdeal ℝ L), lowerCentralSeries ℝ L L (bracketWordDepth a)⁆).neg_mem hh

theorem evalBracketWord_eq_zero_of_depth
    (X : I → L) {k : ℕ} (hk : lowerCentralSeries ℝ L L k = ⊥)
    (w : FreeMagma I) (hw : k ≤ bracketWordDepth w) : evalBracketWord X w = 0 := by
  have h := antitone_lowerCentralSeries ℝ L L hw
    (evalBracketWord_mem_lowerCentralSeries X w)
  rw [hk] at h
  exact h

variable [Fintype I] [DecidableEq I]

def boundedBracketWords : ℕ → Finset (FreeMagma I)
  | 0 => ∅
  | k + 1 => Finset.univ.image FreeMagma.of ∪
      ((boundedBracketWords k).product (boundedBracketWords k)).image
        (fun p => p.1 * p.2)

@[simp] theorem mem_boundedBracketWords (w : FreeMagma I) (k : ℕ) :
    w ∈ boundedBracketWords (I := I) k ↔ bracketWordDepth w < k := by
  induction k generalizing w with
  | zero => simp [boundedBracketWords]
  | succ k ih =>
    cases w with
    | of i => simp [boundedBracketWords, bracketWordDepth]
    | mul a b =>
      rw [boundedBracketWords, Finset.mem_union]
      have hn : a * b ∉ Finset.univ.image (FreeMagma.of : I → FreeMagma I) := by
        rintro he
        obtain ⟨i, _, hi⟩ := Finset.mem_image.mp he
        cases hi
      change (a * b ∈ Finset.univ.image FreeMagma.of ∨
        a * b ∈ ((boundedBracketWords k).product (boundedBracketWords k)).image
          (fun p => p.1 * p.2)) ↔
          max (bracketWordDepth a) (bracketWordDepth b) + 1 < k + 1
      rw [or_iff_right hn, Finset.mem_image]
      constructor
      · rintro ⟨⟨c, d⟩, hcd, he⟩
        have hab : c = a ∧ d = b := by cases he; exact ⟨rfl, rfl⟩
        rcases hab with ⟨rfl, rfl⟩
        have hh := Finset.mem_product.mp hcd
        exact Nat.add_lt_add_right (max_lt ((ih _).mp hh.1) ((ih _).mp hh.2)) 1
      · intro hh
        have hab : bracketWordDepth a < k ∧ bracketWordDepth b < k :=
          max_lt_iff.mp (Nat.lt_of_add_lt_add_right hh)
        exact ⟨(a, b), Finset.mem_product.mpr
          ⟨(ih a).mpr hab.1, (ih b).mpr hab.2⟩, rfl⟩

/-- Every omitted word evaluates to zero, so this finite list has the same
linear span as the set of all words. -/
theorem span_boundedBracketWords (X : I → L) {k : ℕ}
    (hk : lowerCentralSeries ℝ L L k = ⊥) :
    Submodule.span ℝ (evalBracketWord X '' (↑(boundedBracketWords (I := I) k) : Set (FreeMagma I))) =
      (LieSubalgebra.lieSpan ℝ L (Set.range X)).toSubmodule := by
  rw [← span_evalBracketWord]
  apply le_antisymm
  · exact Submodule.span_mono (Set.image_subset_range _ _)
  · apply Submodule.span_le.mpr
    rintro _ ⟨w, rfl⟩
    by_cases hw : bracketWordDepth w < k
    · exact Submodule.subset_span ⟨w, (mem_boundedBracketWords w k).mpr hw, rfl⟩
    · rw [evalBracketWord_eq_zero_of_depth X hk w (Nat.le_of_not_lt hw)]
      exact Submodule.zero_mem _

/-- Nilpotence supplies a finite spanning word list for every finite generating
family; no finite-dimensionality assumption is needed for this step. -/
theorem exists_finite_spanning_bracketWords [LieRing.IsNilpotent L]
    (X : I → L) (hX : LieSubalgebra.lieSpan ℝ L (Set.range X) = ⊤) :
    ∃ k : ℕ, Submodule.span ℝ
      (evalBracketWord X '' (↑(boundedBracketWords (I := I) k) : Set (FreeMagma I))) = ⊤ := by
  obtain ⟨k, hk⟩ := LieModule.IsNilpotent.nilpotent ℝ L L
  exact ⟨k, by rw [span_boundedBracketWords X hk, hX]; rfl⟩

end PolycyclicRecognition

end

end OAI
