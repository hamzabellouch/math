import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialBoxRadius

namespace OAI

/-! # Fitting an arbitrary logarithm into a positive-width unit box -/

noncomputable section
namespace PolycyclicRecognition

open Module

theorem norm_box_at_logarithmic_scale_le_one
    {L J : Type*} [LieRing L] [LieAlgebra ℝ L] [Fintype J]
    (b : Basis J ℝ L) (cost : J → ℝ) {lo : ℝ} (hlo : 0 < lo)
    (hcost : ∀ j, lo ≤ cost j) (v : L) :
    ‖(exponentialRescaleBasis b cost (Real.log (2 + ‖b.equivFun v‖) / lo)).equivFun v‖ ≤ 1 := by
  let R := ‖b.equivFun v‖
  let r := Real.log (2 + R) / lo
  have hR : 0 ≤ R := norm_nonneg _
  have hr : 0 ≤ r := div_nonneg (Real.log_nonneg (by linarith)) hlo.le
  have he : r * lo = Real.log (2 + R) := div_mul_cancel₀ _ hlo.ne'
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro j
  change |(exponentialRescaleBasis b cost r).repr v j| ≤ 1
  simp only [exponentialRescaleBasis, Basis.repr_unitsSMul, Units.smul_def,
    Units.val_inv_eq_inv_val, Units.val_mk0, smul_eq_mul, ← Real.exp_neg,
    abs_mul, abs_of_pos (Real.exp_pos _)]
  have hj : |b.repr v j| ≤ R := norm_le_pi_norm (b.equivFun v) j
  calc
    _ ≤ Real.exp (-(r * lo)) * R :=
      mul_le_mul (Real.exp_le_exp.mpr (by nlinarith [hcost j])) hj
        (abs_nonneg _) (Real.exp_nonneg _)
    _ = R / (2 + R) := by
      rw [he, Real.exp_neg, Real.exp_log (by linarith)]
      ring
    _ ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)

end PolycyclicRecognition

end

end OAI
