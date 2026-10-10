import OAI.Combinatorics.DiscreteConvexity.FourierWeights
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace OAI

/-!
# Orthogonality of the biased product kernel

The two possible choices at one coordinate give its Bernoulli diagonal
matrix. Summing over all subsets tensors this identity, with no square roots
or choice of a normalized Fourier basis.
-/

noncomputable section
open scoped BigOperators

namespace TalagrandDiscreteConvexity

/-- The one-coordinate Gram identity for the mass and alternating factors. -/
theorem bitWeight_correction_gram (q : ℝ) (hq1 : q < 1) (x y : Bool) :
    bitWeight q x * bitWeight q y +
        (q / (1 - q)) * correction q x * correction q y =
      if x = y then bitWeight q x else 0 := by
  have hden : (1 : ℝ) - q ≠ 0 := ne_of_gt (sub_pos.mpr hq1)
  cases x <;> cases y <;>
    simp [bitWeight, correction] <;> field_simp [hden] <;> ring

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Move the subset weight into the coordinate product. -/
theorem rowKernel_weighted_product (q : ℝ) (U : Finset V) (x y : V → Bool) :
    (q / (1 - q)) ^ U.card * rowKernel q U x * rowKernel q U y =
      ∏ i, if i ∈ U then
        (q / (1 - q)) * correction q (x i) * correction q (y i)
      else bitWeight q (x i) * bitWeight q (y i) := by
  have hp : (q / (1 - q)) ^ U.card =
      ∏ i : V, if i ∈ U then q / (1 - q) else 1 := by
    symm
    rw [Finset.prod_ite_mem_eq, Finset.prod_const]
  rw [hp]
  simp only [rowKernel]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ U <;> simp [hi]

/-- Summing the weighted kernel products over all subsets gives the original
Bernoulli mass on the diagonal and zero away from the diagonal. -/
theorem rowKernel_gram (q : ℝ) (_hq0 : 0 < q) (hq1 : q < 1) (x y : V → Bool) :
    (∑ U : Finset V,
      (q / (1 - q)) ^ U.card * rowKernel q U x * rowKernel q U y) =
      if x = y then cubeWeight q x else 0 := by
  classical
  calc
    (∑ U : Finset V,
        (q / (1 - q)) ^ U.card * rowKernel q U x * rowKernel q U y) =
        ∑ U : Finset V, ∏ i, if i ∈ U then
          (q / (1 - q)) * correction q (x i) * correction q (y i)
        else bitWeight q (x i) * bitWeight q (y i) := by
      apply Finset.sum_congr rfl
      intro U _
      exact rowKernel_weighted_product q U x y
    _ = ∏ i,
        ((q / (1 - q)) * correction q (x i) * correction q (y i) +
          bitWeight q (x i) * bitWeight q (y i)) := by
      simpa using (sum_finset_product (fun (i : V) (flag : Bool) =>
        if flag then
          (q / (1 - q)) * correction q (x i) * correction q (y i)
        else bitWeight q (x i) * bitWeight q (y i)))
    _ = ∏ i, if x i = y i then bitWeight q (x i) else 0 := by
      apply Finset.prod_congr rfl
      intro i _
      rw [add_comm]
      exact bitWeight_correction_gram q hq1 (x i) (y i)
    _ = if x = y then cubeWeight q x else 0 := by
      rw [Fintype.prod_ite_zero]
      by_cases hxy : x = y
      · have hpoint : ∀ i, x i = y i := fun i => congrFun hxy i
        simp only [ite_eq_left hpoint, ite_eq_left hxy, cubeWeight]
      · have hpoint : ¬ ∀ i, x i = y i := fun h => hxy (funext h)
        simp only [ite_eq_right hpoint, ite_eq_right hxy]

end TalagrandDiscreteConvexity

end

end OAI
