import OAI.Combinatorics.ContingencyTables.Transport.FiniteLawMoments
import Mathlib.Logic.Equiv.Prod

namespace OAI

/-! # Coordinate marginals and a union bound for independent finite blocks -/

namespace ContingencyTables.FiniteIndependentAverages

open CommonBasesFPRAS
open scoped BigOperators Classical

noncomputable section

lemma uniformAverage_coordinate {J : Type*} [Fintype J] {X : J → Type*}
    [∀ j,Fintype (X j)] [∀ j,Nonempty (X j)] (i : J) (g : X i → ℝ) :
    uniformAverage (fun x : (j : J) → X j => g (x i))=uniformAverage g := by
  have he := uniformAverage_equiv (Equiv.piSplitAt i X) (fun x => g x.1)
  change uniformAverage (fun x : (j : J) → X j => g (x i))=
    uniformAverage (fun x : X i × ((j : {j // j≠i}) → X j.val) => g x.1) at he
  rw [he,uniformAverage_prod]
  simp_rw [uniformAverage_const]

lemma uniform_union_bound {X J : Type*} [Fintype X] [Fintype J]
    (bad : J → X → Prop) :
    uniformAverage (fun x => if ∃ j,bad j x then (1:ℝ) else 0) ≤
      ∑ j,uniformAverage (fun x => if bad j x then (1:ℝ) else 0) := by
  rw [←uniformAverage_sum]
  apply uniformAverage_mono
  intro x
  by_cases h : ∃ j,bad j x
  · obtain ⟨j,hj⟩ := h
    rw [ite_eq_left ⟨j,hj⟩]
    calc
      1 = (if bad j x then (1:ℝ) else 0) := by rw [ite_eq_left hj]
      _ ≤ ∑ k : J,if bad k x then (1:ℝ) else 0 :=
        Finset.single_le_sum (f := fun k => if bad k x then (1:ℝ) else 0)
          (fun k _ => by split_ifs <;> norm_num) (Finset.mem_univ j)
  · rw [ite_eq_right h]
    exact Finset.sum_nonneg (fun j _ => by split_ifs <;> norm_num)

/-- Each block is an actual independently uniform finite experiment.
The event may test a different observable on each block. -/
theorem independent_union_failure {J : Type*} [Fintype J] {X : J → Type*}
    [∀ j,Fintype (X j)] [∀ j,Nonempty (X j)] (bad : (j : J) → X j → Prop) :
    uniformAverage (fun draws : (j : J) → X j =>
      if ∃ j,bad j (draws j) then (1:ℝ) else 0) ≤
      ∑ j,uniformAverage (fun x : X j => if bad j x then (1:ℝ) else 0) := by
  apply (uniform_union_bound (fun j (draws : (k : J) → X k) => bad j (draws j))).trans_eq
  apply Finset.sum_congr rfl
  intro j _
  exact uniformAverage_coordinate j (fun x => if bad j x then (1:ℝ) else 0)

end

end ContingencyTables.FiniteIndependentAverages

end OAI
