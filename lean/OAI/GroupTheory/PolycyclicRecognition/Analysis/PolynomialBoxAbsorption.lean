import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialBoxRadius

namespace OAI

/-! # Absorbing polynomial box radii at an affine larger scale -/

noncomputable section
namespace PolycyclicRecognition

open Module

theorem polynomial_radius_le_exponential {C r : ℝ} (_hC : 0 ≤ C) (hr : 0 ≤ r) (p : ℕ) :
    C * (1 + r) ^ p ≤ Real.exp (Real.log (max C 1) + (p : ℝ) * r) := by
  have hD : 0 < max C 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hp : (1 + r) ^ p ≤ (Real.exp r) ^ p :=
    pow_le_pow_left₀ (by linarith) (by simpa [add_comm] using Real.add_one_le_exp r) p
  rw [Real.exp_add, Real.exp_log hD, Real.exp_nat_mul]
  exact mul_le_mul (le_max_left _ _) hp (by positivity) (le_of_lt hD)

theorem exists_affine_scale_absorbing_polynomial
    {L J : Type*} [LieRing L] [LieAlgebra ℝ L] [Fintype J]
    (b : Basis J ℝ L) (cost : J → ℝ) {lo : ℝ} (hlo : 0 < lo)
    (hcost : ∀ j, lo ≤ cost j) {C : ℝ} (hC : 0 ≤ C) (p : ℕ) :
    ∃ A B : ℝ, 1 ≤ A ∧ 0 ≤ B ∧ ∀ r : ℝ, 0 ≤ r → ∀ v : L,
      ‖(exponentialRescaleBasis b cost r).equivFun v‖ ≤ C * (1 + r) ^ p →
      ‖(exponentialRescaleBasis b cost (A * r + B)).equivFun v‖ ≤ 1 := by
  let A := 1 + (p : ℝ) / lo
  let B := Real.log (max C 1) / lo
  have hlog : 0 ≤ Real.log (max C 1) := Real.log_nonneg (le_max_right _ _)
  have hA : 1 ≤ A := by
    have hp := div_nonneg (Nat.cast_nonneg p : (0 : ℝ) ≤ p) hlo.le
    dsimp [A]
    linarith
  have hB : 0 ≤ B := div_nonneg hlog hlo.le
  refine ⟨A, B, hA, hB, fun r hr v hv => ?_⟩
  let t := (p : ℝ) / lo * r + B
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have he : A * r + B = r + t := by dsimp [A, t]; ring
  have htlo : t * lo = (p : ℝ) * r + Real.log (max C 1) := by
    dsimp [t, B]
    field_simp
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro j
  change |(exponentialRescaleBasis b cost (A * r + B)).repr v j| ≤ 1
  rw [he, repr_shift_exponentialRescaleBasis, abs_mul, abs_of_pos (Real.exp_pos _)]
  have hcoord := (norm_le_pi_norm ((exponentialRescaleBasis b cost r).equivFun v) j).trans hv
  have hdecay : Real.exp (-t * cost j) ≤ Real.exp (-t * lo) := by
    apply Real.exp_le_exp.mpr
    nlinarith [hcost j]
  calc
    Real.exp (-t * cost j) * |(exponentialRescaleBasis b cost r).repr v j| ≤
        Real.exp (-t * lo) * (C * (1 + r) ^ p) :=
      mul_le_mul hdecay hcoord (abs_nonneg _) (Real.exp_pos _).le
    _ ≤ Real.exp (-t * lo) * Real.exp (Real.log (max C 1) + (p : ℝ) * r) :=
      mul_le_mul_of_nonneg_left (polynomial_radius_le_exponential hC hr p) (Real.exp_pos _).le
    _ = 1 := by
      rw [← Real.exp_add, neg_mul, htlo]
      have hz : -((p : ℝ) * r + Real.log (max C 1)) +
          (Real.log (max C 1) + (p : ℝ) * r) = 0 := by ring
      rw [hz, Real.exp_zero]

end PolycyclicRecognition

end

end OAI
