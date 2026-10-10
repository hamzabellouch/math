import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.OddPowerNonlinearity
import Mathlib.Analysis.SpecificLimits.Normed

namespace OAI

/-! Small polynomial nonlinearities on the subunit annulus used on the exterior. -/

namespace DefocusingNLS

open Filter

theorem radial_oddPower_norm (m : ℕ) (z : ℂ) :
    ‖oddPowerNonlinearity m z‖ = ‖z‖^(2*m+1) := by
  rw [oddPowerNonlinearity_eq,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (norm_nonneg _) _),pow_succ]

theorem radial_oddPower_succ (m : ℕ) (z : ℂ) :
    oddPowerNonlinearity (m+1) z=oddPowerNonlinearity m z*star z*z := by
  simp only [oddPowerNonlinearity,pow_succ]
  ring

theorem radial_oddPower_difference (m : ℕ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (z w : ℂ) (hz : ‖z‖ ≤ ρ) (hw : ‖w‖ ≤ ρ) :
    ‖oddPowerNonlinearity m z-oddPowerNonlinearity m w‖ ≤
      (2*(m : ℝ)+1)*ρ^(2*m)*‖z-w‖ := by
  induction m with
  | zero => simp [oddPowerNonlinearity]
  | succ m ih =>
    have hNw : ‖oddPowerNonlinearity m w‖ ≤ ρ^(2*m+1) := by
      rw [radial_oddPower_norm]
      exact pow_le_pow_left₀ (norm_nonneg _) hw _
    have he : oddPowerNonlinearity (m+1) z-oddPowerNonlinearity (m+1) w =
        (oddPowerNonlinearity m z-oddPowerNonlinearity m w)*star z*z+
        oddPowerNonlinearity m w*(star z-star w)*z+
        oddPowerNonlinearity m w*star w*(z-w) := by
      rw [radial_oddPower_succ,radial_oddPower_succ]
      ring
    rw [he]
    calc
      _ ≤ ‖(oddPowerNonlinearity m z-oddPowerNonlinearity m w)*star z*z‖+
          ‖oddPowerNonlinearity m w*(star z-star w)*z‖+
          ‖oddPowerNonlinearity m w*star w*(z-w)‖ := @norm_add₃_le ℂ _ _ _ _
      _ = ‖oddPowerNonlinearity m z-oddPowerNonlinearity m w‖*‖z‖*‖z‖+
          ‖oddPowerNonlinearity m w‖*‖z-w‖*‖z‖+
          ‖oddPowerNonlinearity m w‖*‖w‖*‖z-w‖ := by
        simp only [norm_mul,norm_star,← star_sub]
      _ ≤ ((2*(m : ℝ)+1)*ρ^(2*m)*‖z-w‖)*ρ*ρ+
          ρ^(2*m+1)*‖z-w‖*ρ+ρ^(2*m+1)*ρ*‖z-w‖ := by
        gcongr
      _ = _ := by
        simp only [Nat.mul_add,Nat.mul_one,pow_succ,Nat.cast_add,Nat.cast_one]
        ring

theorem radial_oddPower_lipschitz_tendsto (ρ : ℝ) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Tendsto (fun m : ℕ => (2*(m : ℝ)+1)*ρ^(2*m)) atTop (nhds 0) := by
  have hq : ρ^2 < 1 := pow_lt_one₀ hρ hρ1 (by decide : 2 ≠ 0)
  have h0 := tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg ρ) hq
  have h1 := tendsto_pow_const_mul_const_pow_of_lt_one 1 (sq_nonneg ρ) hq
  convert (h1.const_mul 2).add h0 using 1
  · funext m
    simp only [pow_one,← pow_mul]
    ring
  · ring_nf

end DefocusingNLS

end OAI
