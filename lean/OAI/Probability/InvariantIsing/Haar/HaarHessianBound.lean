import OAI.Probability.InvariantIsing.Haar.HaarFunctionalCurvature

namespace OAI

/-! The antisymmetric part of a finite Hessian controls the curvature term. -/
noncomputable section
open scoped BigOperators
namespace InvariantIsing

theorem sum_antisymmetric_square_le {J : Type*} [Fintype J] (H : J → J → ℝ) :
    (∑ i, ∑ j, (H i j-H j i)^2) ≤ 4*(∑ i, ∑ j, (H i j)^2) := by
  calc
    (∑ i, ∑ j, (H i j-H j i)^2) ≤
        ∑ i, ∑ j, 2*((H i j)^2+(H j i)^2) := by
      apply Finset.sum_le_sum; intro i _
      apply Finset.sum_le_sum; intro j _
      nlinarith [sq_nonneg (H i j+H j i)]
    _ = 4*(∑ i, ∑ j, (H i j)^2) := by
      simp only [mul_add,Finset.mul_sum,Finset.sum_add_distrib]
      rw [Finset.sum_comm (f := fun i j => 2*(H j i)^2)]
      simp only [← Finset.mul_sum]
      ring

end InvariantIsing

end

end OAI
