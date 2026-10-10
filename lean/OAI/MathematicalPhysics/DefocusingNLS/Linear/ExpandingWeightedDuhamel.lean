import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingDuhamel
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace OAI

/-! # Exponentially weighted inhomogeneous estimates

The Bielecki weight gives a contraction on any finite time slab.  The
constant depends on the reaction bound, while the starting radius drops out.
-/

open Set MeasureTheory

namespace DefocusingNLS

private theorem integral_exp_mul_Icc (η t : ℝ) (hη : 0 < η) (ht : 0 ≤ t) :
    (∫ τ in Icc 0 t, Real.exp (η * τ)) = η⁻¹ * (Real.exp (η * t) - 1) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht]
  rw [intervalIntegral.integral_comp_mul_left Real.exp hη.ne', integral_exp]
  simp only [mul_zero, Real.exp_zero, smul_eq_mul]

/-- A forcing bounded by `C exp(η t)` has weighted response at most `C/η`. -/
theorem expandingDuhamel_weighted_norm_le (a b k L η t C : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (hη : 0 < η) (ht : 0 ≤ t) (hC : 0 ≤ C)
    (r : ℝ → FourierL2) (hbound : ∀ τ ∈ Icc 0 t, ‖r τ‖ ≤ C * Real.exp (η * τ)) :
    Real.exp (-η * t) * ‖expandingDuhamel a b k L ha hk hL t r‖ ≤ C / η := by
  have hg : IntegrableOn (fun τ => C * Real.exp (η * τ)) (Icc 0 t) :=
    (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).continuousOn.integrableOn_compact
      isCompact_Icc
  have hi : ‖expandingDuhamel a b k L ha hk hL t r‖ ≤
      ∫ τ in Icc 0 t, C * Real.exp (η * τ) := by
    apply norm_integral_le_of_norm_le hg
    filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
    rw [expandingDuhamelIntegrand_of_mem _ _ _ _ _ _ _ _ _ _ hτ]
    apply (expandingFreeStep_norm_bound a b k (expandingRadius L τ) (t - τ) ha hk
      (hL.trans (expandingRadius_ge L τ hL hτ.1)) (sub_nonneg.mpr hτ.2) (r τ)).trans
    exact (mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr (by
      nlinarith [hτ.2]))).trans (hbound τ hτ)
  rw [integral_const_mul, integral_exp_mul_Icc η t hη ht] at hi
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
