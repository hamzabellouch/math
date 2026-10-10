import OAI.GroupTheory.PolycyclicRecognition.Algebra.RescaledBasisChange

namespace OAI

/-! # Changing the physical scale of one exponential basis -/

namespace PolycyclicRecognition

open Module

variable {L J : Type*} [LieRing L] [LieAlgebra ℝ L]

theorem repr_scale_exponentialRescaleBasis (b : Basis J ℝ L)
    (c : J → ℝ) (r t : ℝ) (x : L) (j : J) :
    (exponentialRescaleBasis b c r).repr x j =
      (exponentialRescaleBasis b c t).repr x j * Real.exp ((t - r) * c j) := by
  simp only [exponentialRescaleBasis, Basis.repr_unitsSMul, Units.smul_def,
    Units.val_inv_eq_inv_val, Units.val_mk0, smul_eq_mul, ← Real.exp_neg]
  have he : Real.exp (-(t * c j)) * Real.exp ((t - r) * c j) =
      Real.exp (-(r * c j)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [mul_right_comm, he]

/-- The exact change in scale is bounded by the largest change in a
coordinate exponent. There is no asymptotic hypothesis in this estimate. -/
theorem norm_scale_exponentialRescaleBasis_le [Fintype J]
    (b : Basis J ℝ L) (c : J → ℝ) (r t A : ℝ)
    (hgap : ∀ j, (t - r) * c j ≤ A) (x : L) :
    ‖(exponentialRescaleBasis b c r).equivFun x‖ ≤
      Real.exp A * ‖(exponentialRescaleBasis b c t).equivFun x‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))).mpr
  intro j
  change |(exponentialRescaleBasis b c r).repr x j| ≤ _
  rw [repr_scale_exponentialRescaleBasis, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ ‖(exponentialRescaleBasis b c t).equivFun x‖ * Real.exp A :=
      mul_le_mul (norm_le_pi_norm ((exponentialRescaleBasis b c t).equivFun x) j)
        (Real.exp_le_exp.mpr (hgap j)) (Real.exp_pos _).le (norm_nonneg _)
    _ = _ := mul_comm _ _

end PolycyclicRecognition

end OAI
