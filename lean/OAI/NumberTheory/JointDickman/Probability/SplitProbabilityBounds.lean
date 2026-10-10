import OAI.NumberTheory.JointDickman.Probability.TwoSiteSplitModel

namespace OAI

/-! # Finite event bounds for the actual two-site split law -/

namespace JointDickman

open Finset

theorem twoSiteSplitProbability_nonneg (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (E : TwoSiteSplit P → Prop) : 0 ≤ twoSiteSplitProbability P E := by
  classical
  apply sum_nonneg
  intro x _
  split_ifs
  · exact twoSiteSplitMass_nonneg P hP x
  · exact le_rfl

theorem twoSiteSplitProbability_congr (P : Finset ℕ) {E F : TwoSiteSplit P → Prop}
    (h : ∀ x, E x ↔ F x) : twoSiteSplitProbability P E = twoSiteSplitProbability P F := by
  classical
  unfold twoSiteSplitProbability
  apply sum_congr rfl
  intro x _
  simp only [h x]

theorem twoSiteSplitProbability_mono (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {E F : TwoSiteSplit P → Prop} (h : ∀ x, E x → F x) :
    twoSiteSplitProbability P E ≤ twoSiteSplitProbability P F := by
  classical
  apply sum_le_sum
  intro x _
  have hm := twoSiteSplitMass_nonneg P hP x
  by_cases he : E x
  · simp only [he, h x he, ite_true, le_refl]
  · simp only [he, ite_false]
    split_ifs <;> first | exact hm | exact le_rfl

theorem twoSiteSplitProbability_or (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (E F : TwoSiteSplit P → Prop) :
    twoSiteSplitProbability P (fun x => E x ∨ F x) ≤
      twoSiteSplitProbability P E + twoSiteSplitProbability P F := by
  classical
  unfold twoSiteSplitProbability
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro x _
  have hm := twoSiteSplitMass_nonneg P hP x
  by_cases he : E x <;> by_cases hf : F x <;> simp [he, hf]
  all_goals linarith only [hm]

/-- A finite event cover costs the sum of the actual event probabilities. -/
theorem twoSiteSplitProbability_cover {ι : Type*} [DecidableEq ι]
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (I : Finset ι)
    (E N : TwoSiteSplit P → Prop) (F : ι → TwoSiteSplit P → Prop)
    (hcover : ∀ x, E x → N x ∨ ∃ i ∈ I, F i x) :
    twoSiteSplitProbability P E ≤ twoSiteSplitProbability P N +
      ∑ i ∈ I, twoSiteSplitProbability P (F i) := by
  classical
  unfold twoSiteSplitProbability
  rw [← sum_comm, ← sum_add_distrib]
  apply sum_le_sum
  intro x _
  have hm := twoSiteSplitMass_nonneg P hP x
  have hsum : 0 ≤ ∑ i ∈ I, if F i x then twoSiteSplitMass P x else 0 := by
    apply sum_nonneg
    intro i _
    split_ifs <;> first | exact hm | exact le_rfl
  have hn : 0 ≤ if N x then twoSiteSplitMass P x else 0 := by
    split_ifs <;> first | exact hm | exact le_rfl
  by_cases he : E x
  · simp only [he, ite_true]
    rcases hcover x he with hN | ⟨i, hi, hFi⟩
    · simp only [hN, ite_true]
      linarith only [hsum]
    · have hterm : twoSiteSplitMass P x ≤ ∑ j ∈ I, if F j x then twoSiteSplitMass P x else 0 := by
        have hh := single_le_sum (fun j (_hj : j ∈ I) => show 0 ≤ if F j x then twoSiteSplitMass P x else 0 by
          split_ifs <;> first | exact hm | exact le_rfl) hi
        simpa only [hFi, ite_true] using hh
      linarith only [hn, hterm]
  · simp only [he, ite_false]
    exact add_nonneg hn hsum


theorem twoSiteSplitProbability_four_or (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (A B C D : TwoSiteSplit P → Prop) :
    twoSiteSplitProbability P (fun x => A x ∨ B x ∨ C x ∨ D x) ≤
      twoSiteSplitProbability P A + twoSiteSplitProbability P B +
        twoSiteSplitProbability P C + twoSiteSplitProbability P D := by
  calc
    _ ≤ twoSiteSplitProbability P A + twoSiteSplitProbability P (fun x => B x ∨ C x ∨ D x) :=
      twoSiteSplitProbability_or P hP A (fun x => B x ∨ C x ∨ D x)
    _ ≤ twoSiteSplitProbability P A +
        (twoSiteSplitProbability P B + twoSiteSplitProbability P (fun x => C x ∨ D x)) :=
      add_le_add le_rfl (twoSiteSplitProbability_or P hP B (fun x => C x ∨ D x))
    _ ≤ twoSiteSplitProbability P A +
        (twoSiteSplitProbability P B + (twoSiteSplitProbability P C + twoSiteSplitProbability P D)) :=
      add_le_add le_rfl (add_le_add le_rfl (twoSiteSplitProbability_or P hP C D))
    _ = _ := by ring

end JointDickman

end OAI
