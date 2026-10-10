import OAI.Probability.FreeIsing.Estimates.RadialRepresentation

namespace OAI

noncomputable section

namespace Problem367
namespace RadialWalk

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem norm_power_sq_eq_inner_double (A : H →L[ℝ] H)
    (hA : (A : H →ₗ[ℝ] H).IsSymmetric) (x : H) (n : ℕ) :
    ‖(A ^ n) x‖ ^ 2 = inner ℝ x ((A ^ (2 * n)) x) := by
  have hp : ((A ^ n : H →L[ℝ] H) : H →ₗ[ℝ] H).IsSymmetric := by
    simpa only [ContinuousLinearMap.toLinearMap_pow] using hA.pow n
  calc
    ‖(A ^ n) x‖ ^ 2 = inner ℝ ((A ^ n) x) ((A ^ n) x) :=
      (real_inner_self_eq_norm_sq _).symm
    _ = inner ℝ x ((A ^ n) ((A ^ n) x)) := hp x ((A ^ n) x)
    _ = inner ℝ x ((A ^ (2 * n)) x) := by
      rw [show 2 * n = n + n by omega, pow_add]
      rfl

theorem norm_power_sq_le_of_radial_bound {d : ℕ}
    (S : Fin d → H →L[ℝ] H) (hS : ∀ c, S c * S c = 1)
    (hA : (operatorAverage S : H →ₗ[ℝ] H).IsSymmetric)
    (hd : 3 ≤ d) (x : H) {C : ℝ} (hC : 0 ≤ C)
    (hcov : ∀ v, |inner ℝ x (wordOperator S v x)| ≤ C * treeWeight d v)
    (n : ℕ) :
    ‖(operatorAverage S ^ n) x‖ ^ 2 ≤ C * rate d ^ (2 * n) := by
  rw [norm_power_sq_eq_inner_double _ hA]
  exact (le_abs_self _).trans (matrix_coefficient_power_bound S hS hd x hC hcov (2 * n))

theorem norm_power_le_of_radial_bound {d : ℕ}
    (S : Fin d → H →L[ℝ] H) (hS : ∀ c, S c * S c = 1)
    (hA : (operatorAverage S : H →ₗ[ℝ] H).IsSymmetric)
    (hd : 3 ≤ d) (x : H) {C : ℝ} (hC : 0 ≤ C)
    (hcov : ∀ v, |inner ℝ x (wordOperator S v x)| ≤ C * treeWeight d v)
    (n : ℕ) :
    ‖(operatorAverage S ^ n) x‖ ≤ Real.sqrt C * rate d ^ n := by
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg (rate_nonneg d) n))).mp
  calc
    ‖(operatorAverage S ^ n) x‖ ^ 2 ≤ C * rate d ^ (2 * n) :=
      norm_power_sq_le_of_radial_bound S hS hA hd x hC hcov n
    _ = (Real.sqrt C * rate d ^ n) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hC, ← pow_mul]
      rw [Nat.mul_comm n 2]

end RadialWalk
end Problem367

end

end OAI
