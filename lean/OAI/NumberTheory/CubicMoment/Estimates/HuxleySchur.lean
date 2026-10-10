import OAI.NumberTheory.CubicMoment.Estimates.HuxleyDuality

namespace OAI

/-! The finite Schur estimate used for the Gaussian additive-sieve kernel. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma huxley_finite_schur {ι : Type*} (P : Finset ι) (K : ι → ι → ℝ)
    (hK : ∀ i ∈ P, ∀ j ∈ P, 0 ≤ K i j)
    (hsym : ∀ i ∈ P, ∀ j ∈ P, K i j = K j i)
    {B : ℝ} (hrow : ∀ i ∈ P, ∑ j ∈ P, K i j ≤ B) (v : ι → ℂ) :
    (∑ i ∈ P, ∑ j ∈ P, ‖v i‖*‖v j‖*K i j) ≤ B*∑ i ∈ P, ‖v i‖^2 := by
  have hcol : (∑ i ∈ P, ∑ j ∈ P, ‖v j‖^2*K i j) =
      ∑ i ∈ P, ∑ j ∈ P, ‖v i‖^2*K i j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hsym j hj i hi]
  have he : (∑ i ∈ P, ∑ j ∈ P, (‖v i‖^2+‖v j‖^2)*K i j) =
      2*∑ i ∈ P, ‖v i‖^2*(∑ j ∈ P, K i j) := by
    simp_rw [add_mul,Finset.sum_add_distrib]
    rw [hcol]
    simp_rw [← Finset.mul_sum]
    ring
  have hpair : 2*(∑ i ∈ P, ∑ j ∈ P, ‖v i‖*‖v j‖*K i j) ≤
      ∑ i ∈ P, ∑ j ∈ P, (‖v i‖^2+‖v j‖^2)*K i j := by
    simp_rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    have hp : 2*‖v i‖*‖v j‖ ≤ ‖v i‖^2+‖v j‖^2 := by
      nlinarith [sq_nonneg (‖v i‖-‖v j‖)]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hp (hK i hi j hj)
  have htotal : (∑ i ∈ P, ‖v i‖^2*(∑ j ∈ P, K i j)) ≤ B*∑ i ∈ P, ‖v i‖^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hrow i hi) (sq_nonneg ‖v i‖)
  rw [he] at hpair
  linarith

end CubicFirstMoment

end

end OAI
