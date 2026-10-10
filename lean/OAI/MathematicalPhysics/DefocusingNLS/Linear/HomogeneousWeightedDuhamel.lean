import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousDuhamel
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace OAI

/-! # Exponential time weights for whole-space inhomogeneous evolution -/

open Set MeasureTheory

namespace DefocusingNLS

attribute [local irreducible] homogeneousFreeOperator

private theorem homogeneous_integral_exp_Icc (η t : ℝ) (hη : 0 < η) (ht : 0 ≤ t) :
    (∫ τ in Icc 0 t, Real.exp (η * τ)) = η⁻¹ * (Real.exp (η * t) - 1) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht]
  rw [intervalIntegral.integral_comp_mul_left Real.exp hη.ne', integral_exp]
  simp only [mul_zero, Real.exp_zero, smul_eq_mul]

/-- An exponentially bounded forcing gives the Bielecki contraction estimate. -/
theorem homogeneousDuhamel_weighted_norm_le (a b k η t C : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hη : 0 < η) (ht : 0 ≤ t) (hC : 0 ≤ C)
    (r : ℝ → HomogeneousY a k) (hbound : ∀ τ ∈ Icc 0 t, ‖r τ‖ ≤ C * Real.exp (η * τ)) :
    Real.exp (-η * t) * ‖homogeneousDuhamel a b k ha ha1 hk t r‖ ≤ C / η := by
  have hg : IntegrableOn (fun τ => C * Real.exp (η * τ)) (Icc 0 t) :=
    (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).continuousOn.integrableOn_compact
      isCompact_Icc
  have hi : ‖homogeneousDuhamel a b k ha ha1 hk t r‖ ≤
      ∫ τ in Icc 0 t, C * Real.exp (η * τ) := by
    rw [homogeneousDuhamel, intervalIntegral.integral_of_le ht,
      ← integral_Icc_eq_integral_Ioc]
    apply norm_integral_le_of_norm_le hg
    filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
    apply (homogeneousFreeOperator_forward_bound a b k (t - τ) ha ha1 hk
      (sub_nonneg.mpr hτ.2) (r τ)).trans
    exact (mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr (by
      nlinarith [hτ.2]))).trans (hbound τ hτ)
  rw [integral_const_mul, homogeneous_integral_exp_Icc η t hη ht] at hi
  have he : Real.exp (-η * t) * Real.exp (η * t) = 1 := by
    rw [← Real.exp_add, show -η * t + η * t = 0 by ring, Real.exp_zero]
  calc
    _ ≤ Real.exp (-η * t) * (C * (η⁻¹ * (Real.exp (η * t) - 1))) :=
      mul_le_mul_of_nonneg_left hi (Real.exp_pos _).le
    _ = (C / η) * (Real.exp (-η * t) * Real.exp (η * t) - Real.exp (-η * t)) := by ring
    _ = (C / η) * (1 - Real.exp (-η * t)) := by rw [he]
    _ ≤ C / η := mul_le_of_le_one_right (div_nonneg hC hη.le) (by linarith [Real.exp_pos (-η * t)])

end DefocusingNLS

end OAI
