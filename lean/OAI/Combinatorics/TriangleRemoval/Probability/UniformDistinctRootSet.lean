import Mathlib
import OAI.Combinatorics.TriangleRemoval.Tracking.TriangleDrift
import OAI.Combinatorics.TriangleRemoval.Coupling.UniformRootAtom

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open scoped BigOperators
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave
section RootAverage
variable {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι]

lemma uniform_distinct_root_set_probability_le (G : Finset α) (hne : G.Nonempty)
    (E : Finset α) :
    pmfMean (PMF.uniformOfFinset G hne) (fun x =>
      pmfMean (PMF.uniformOfFinset G hne) (fun y =>
        if x ≠ y ∧ ({x,y} : Finset α) = E then 1 else 0)) ≤
      2/(G.card : ℝ)^2 := by
  by_cases hE : E.card = 2
  · apply le_trans _ (uniform_root_set_probability_le G hne E hE)
    apply pmfMean_mono
    intro x _
    apply pmfMean_mono
    intro y _
    by_cases h : x ≠ y ∧ ({x,y} : Finset α) = E
    · simp [h]
    · simp only [h,ite_false]
      split_ifs <;> norm_num
  · have hz (x y : α) : ¬ (x ≠ y ∧ ({x,y} : Finset α) = E) := by
      rintro ⟨hxy,h⟩
      apply hE
      rw [← h,Finset.card_pair hxy]
    simp only [hz,ite_false,pmfMean_const]
    positivity

theorem uniform_two_root_weighted_sum (G : Finset α) (hne : G.Nonempty)
    (roots : ι → Finset α) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    pmfMean (PMF.uniformOfFinset G hne) (fun x =>
      pmfMean (PMF.uniformOfFinset G hne) (fun y =>
        ∑ i, if x ≠ y ∧ roots i = ({x,y} : Finset α) then w i else 0)) ≤
      (2/(G.card : ℝ)^2) * ∑ i, w i := by
  let p := PMF.uniformOfFinset G hne
  have hpt (x y : α) (i : ι) :
      (if x ≠ y ∧ roots i = ({x,y} : Finset α) then w i else 0) =
        (if x ≠ y ∧ ({x,y} : Finset α) = roots i then 1 else 0)*w i := by
    simp only [eq_comm (a := roots i)]
    split_ifs <;> simp
  simp_rw [hpt,pmfMean_sum,pmfMean_mul_const]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_right (uniform_distinct_root_set_probability_le G hne (roots i)) (hw i)

theorem uniform_one_root_weighted_sum (G : Finset α) (hne : G.Nonempty)
    (root : ι → α) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    pmfMean (PMF.uniformOfFinset G hne) (fun x =>
      ∑ i, if root i = x then w i else 0) ≤
      (1/(G.card : ℝ)) * ∑ i, w i := by
  have hpt (x : α) (i : ι) : (if root i = x then w i else 0) =
      (if x = root i then 1 else 0)*w i := by
    simp only [eq_comm (a := root i)]
    split_ifs <;> simp
  simp_rw [hpt,pmfMean_sum,pmfMean_mul_const,uniform_root_atom]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_right _ (hw i)
  split_ifs <;> first | rfl | positivity

end RootAverage
end SharpTerminalLeave

end

end OAI
