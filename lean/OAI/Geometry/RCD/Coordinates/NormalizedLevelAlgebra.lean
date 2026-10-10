import OAI.Geometry.RCD.Coordinates.NonlinearIteration

namespace OAI

/-! # Normalization algebra for the harmonic level recurrence -/

namespace RegularPointCoordinates

/-- Scaling the level energy by the outer volume removes that volume
from the superlinear recurrence. -/
theorem normalized_level_identity {V J C d a b α : ℝ}
    (hV : 0 < V) (hJ : 0 ≤ J) (ha : 0 < a) (hb : 0 < b) (hα : 0 < α) (i : ℕ) :
    (C*V^(-α)*(d*b^i)*J*(a*b^i*J)^α)/V =
      (C*d*a^α)*(b^(1+α))^i*(J/V)^(1+α) := by
  by_cases hJ0 : J = 0
  · simp only [hJ0,mul_zero,zero_div,Real.zero_rpow hα.ne',
      Real.zero_rpow (by linarith : 1+α ≠ 0)]
  have hJp : 0 < J := lt_of_le_of_ne hJ (Ne.symm hJ0)
  rw [Real.div_rpow hJ hV.le,Real.rpow_add hJp,Real.rpow_add hV,
    Real.rpow_one,Real.rpow_one,Real.rpow_neg hV.le,
    Real.mul_rpow (mul_nonneg ha.le (pow_nonneg hb.le _)) hJ,
    Real.mul_rpow ha.le (pow_nonneg hb.le _),
    ← Real.rpow_pow_comm hb.le α i,Real.rpow_add hb,Real.rpow_one,mul_pow]
  field_simp

/-- The dyadic radii stay between one half and three quarters of R. -/
theorem dyadic_inner_radii {R : ℝ} (hR : 0 < R) (i : ℕ) :
    0 ≤ R/2+R/(4*2^(i+1)) ∧
    R/2+R/(4*2^(i+1)) < R/2+R/(4*2^i) ∧
    R/2+R/(4*2^i) < R := by
  have hp : (0:ℝ) < 2^i := by positivity
  have hge : (1:ℝ) ≤ 2^i := one_le_pow₀ (by norm_num)
  constructor
  · positivity
  constructor
  · rw [pow_succ]
    have hh : R/(4*(2^i*2)) < R/(4*2^i) :=
      div_lt_div_of_pos_left hR (by positivity) (by nlinarith)
    linarith
  · have hh : R/(4*2^i) ≤ R/4 := by
      apply div_le_div_of_nonneg_left hR.le (by norm_num)
      nlinarith
    linarith

/-- The reciprocal squared level gap and the cutoff energy grow by four. -/
theorem dyadic_level_gap_bounds {R : ℝ} (hR : 0 < R) (i : ℕ) :
    0 ≤ 1-(2^i:ℝ)⁻¹ ∧
    1-(2^i:ℝ)⁻¹ < 1-(2^(i+1):ℝ)⁻¹ ∧
    ((1-(2^(i+1):ℝ)⁻¹)-(1-(2^i:ℝ)⁻¹))⁻¹^2 = 4*4^i ∧
    10*R^2*(((R/2+R/(4*2^i))-(R/2+R/(4*2^(i+1))))⁻¹)^2+1 ≤ 641*4^i := by
  have hp : (0:ℝ) < 2^i := by positivity
  have hn : (2^i:ℝ) ≠ 0 := hp.ne'
  have hge : (1:ℝ) ≤ 2^i := one_le_pow₀ (by norm_num)
  have hf : (4:ℝ)^i = (2^i:ℝ)^2 := by
    calc
      (4:ℝ)^i = (2*2:ℝ)^i := by norm_num
      _ = (2^i:ℝ)^2 := by rw [mul_pow,pow_two]
  have hk : 0 ≤ 1-(2^i:ℝ)⁻¹ := by
    have hh : (2^i:ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hge
    linarith
  have hd : (1-(2^(i+1):ℝ)⁻¹)-(1-(2^i:ℝ)⁻¹) = 1/(2*2^i) := by
    rw [pow_succ]
    field_simp
    ring
  have hδ : 0 < (1-(2^(i+1):ℝ)⁻¹)-(1-(2^i:ℝ)⁻¹) := hd ▸ (by positivity)
  refine ⟨hk,by linarith,?_,?_⟩
  · rw [hd,hf]
    field_simp
    ring
  · have hr : (R/2+R/(4*2^i))-(R/2+R/(4*2^(i+1))) = R/(8*2^i) := by
      rw [pow_succ]
      field_simp
      ring
    rw [hr,hf]
    have he : 10*R^2*(R/(8*2^i))⁻¹^2 = 640*(2^i:ℝ)^2 := by
      field_simp
      ring
    rw [he]
    nlinarith [sq_nonneg ((2^i:ℝ)-1)]

end RegularPointCoordinates

end OAI
