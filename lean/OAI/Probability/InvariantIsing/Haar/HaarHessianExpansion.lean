import OAI.Probability.InvariantIsing.Haar.HaarCorrectedHessian

namespace OAI

/-! Finite square completion in the logarithmic Bochner calculation. -/
noncomputable section
open scoped BigOperators
namespace InvariantIsing

lemma sum_gradient_outer_sq {J : Type*} [Fintype J] (g : J → ℝ) :
    (∑ i, ∑ j, (g i*g j)^2) = (∑ i, (g i)^2)^2 := by
  simp only [mul_pow]
  rw [pow_two,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]

lemma sum_corrected_hessian_sq {J : Type*} [Fintype J]
    (H : J → J → ℝ) (g : J → ℝ) (c : ℝ) :
    (∑ i, ∑ j, (H i j-c*g i*g j)^2) =
      (∑ i, ∑ j, (H i j)^2)-2*c*(∑ i, ∑ j, H i j*g i*g j)+
        c^2*(∑ i, (g i)^2)^2 := by
  have hs (i j : J) : (H i j-c*g i*g j)^2 =
      (H i j)^2-2*c*(H i j*g i*g j)+c^2*(g i*g j)^2 := by ring
  simp_rw [hs]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum]
  rw [sum_gradient_outer_sq]

end InvariantIsing

end

end OAI
