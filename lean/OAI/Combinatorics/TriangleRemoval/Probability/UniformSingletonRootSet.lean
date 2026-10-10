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
section
variable {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι]

lemma uniform_singleton_root_set_probability_le (G : Finset α) (hne : G.Nonempty)
    (S : Finset α) :
    pmfMean (PMF.uniformOfFinset G hne) (fun e => if S = {e} then 1 else 0) ≤
      1/(G.card : ℝ) := by
  classical
  by_cases hs : S.card = 1
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hs
    have he : (fun e : α => if ({a} : Finset α) = {e} then (1 : ℝ) else 0) =
        (fun e => if e = a then 1 else 0) := by
      funext e
      simp only [Finset.singleton_inj,eq_comm]
    rw [he,uniform_root_atom]
    split_ifs <;> first | rfl | positivity
  · have he (e : α) : S ≠ {e} := by
      rintro rfl
      simp at hs
    simp only [he,ite_false,pmfMean_const]
    positivity

theorem uniform_singleton_root_weighted_sum (G : Finset α) (hne : G.Nonempty)
    (roots : ι → Finset α) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    pmfMean (PMF.uniformOfFinset G hne) (fun x =>
      ∑ i, if roots i = {x} then w i else 0) ≤
      (1/(G.card : ℝ)) * ∑ i, w i := by
  have hpt (x : α) (i : ι) : (if roots i = {x} then w i else 0) =
      (if roots i = {x} then 1 else 0)*w i := by
    split_ifs <;> simp
  simp_rw [hpt,pmfMean_sum,pmfMean_mul_const]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_right (uniform_singleton_root_set_probability_le G hne (roots i)) (hw i)

end
end SharpTerminalLeave

end

end OAI
