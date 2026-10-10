import OAI.MathematicalPhysics.Boltzmann.Collision.CarlemanNormalCoordinates
import OAI.MathematicalPhysics.Boltzmann.Collision.VelocityWeight

namespace OAI

/-!
# Weight transfer on a collision plane

The exact Gaussian identity and polynomial transfer turn the normalized
gain weight into the tilted cold measure used in `ker:tilted-kernel`.
-/

noncomputable section

open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness.VelocityWeight

def W (q : ℝ) (v : Velocity) : ℝ := 1 + singularity q (transverse v)

theorem W_pos (q : ℝ) (v : Velocity) : 0 < W q v := by
  unfold W
  linarith [singularity_nonneg q (transverse v)]

private theorem rpow_neg_fifty {x : ℝ} (hx : 0 ≤ x) :
    x ^ (-50 : ℝ) = (x ^ (50 : ℕ))⁻¹ := by
  rw [show (-50 : ℝ) = -(50 : ℕ) by norm_num, Real.rpow_neg hx, Real.rpow_natCast]

theorem H_ratio (q : ℝ) (ξ v : Velocity) :
    H q ξ / H q v = (Real.exp (-‖ξ‖ ^ 2) / Real.exp (-‖v‖ ^ 2)) *
      ((1 + ‖v‖ ^ 2) ^ (50 : ℕ) / (1 + ‖ξ‖ ^ 2) ^ (50 : ℕ)) * (W q ξ / W q v) := by
  unfold H
  change (Real.exp (-‖ξ‖ ^ 2) * (1 + ‖ξ‖ ^ 2) ^ (-50 : ℝ) * W q ξ) /
    (Real.exp (-‖v‖ ^ 2) * (1 + ‖v‖ ^ 2) ^ (-50 : ℝ) * W q v) = _
  rw [rpow_neg_fifty (by positivity), rpow_neg_fifty (by positivity)]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

theorem polynomial_ratio_le (p ξ v : Velocity)
    (h : inner ℝ (v - p) (ξ - v) = 0) :
    (1 + ‖v‖ ^ 2) ^ (50 : ℕ) / (1 + ‖ξ‖ ^ 2) ^ (50 : ℕ) ≤
      (1 + ‖p‖ ^ 2) ^ (50 : ℕ) := by
  apply (div_le_iff₀ (by positivity : 0 < (1 + ‖ξ‖ ^ 2) ^ (50 : ℕ))).mpr
  rw [← mul_pow]
  exact pow_le_pow_left₀ (by positivity) (carleman_bracket_sq_le p ξ v h) 50

def tiltConstant : ℝ := Real.exp 1 * (Nat.factorial 50 : ℝ)

theorem tiltConstant_pos : 0 < tiltConstant := by unfold tiltConstant; positivity

theorem polynomial_le_gaussian (p : Velocity) :
    (1 + ‖p‖ ^ 2) ^ (50 : ℕ) ≤ tiltConstant * Real.exp (‖p‖ ^ 2) := by
  have hf : 0 < (Nat.factorial 50 : ℝ) := by positivity
  have h := (div_le_iff₀ hf).mp
    (Real.pow_div_factorial_le_exp (1 + ‖p‖ ^ 2) (by positivity) 50)
  calc
    _ ≤ Real.exp (1 + ‖p‖ ^ 2) * (Nat.factorial 50 : ℝ) := h
    _ = _ := by unfold tiltConstant; rw [Real.exp_add]; ring

/-- The complete weight ratio estimate preceding the tilted-kernel bound. -/
theorem collision_weight_ratio_le (q : ℝ) (p ξ v : Velocity)
    (h : inner ℝ (v - p) (ξ - v) = 0) :
    H q ξ / H q v ≤ tiltConstant *
      Real.exp (2 * ‖p‖ ^ 2 - ‖companionVelocity p ξ v‖ ^ 2) * (W q ξ / W q v) := by
  rw [H_ratio, carleman_gaussian_ratio p ξ v h]
  have hw : 0 ≤ W q ξ / W q v := div_nonneg (W_pos q ξ).le (W_pos q v).le
  calc
    _ ≤ Real.exp (‖p‖ ^ 2 - ‖companionVelocity p ξ v‖ ^ 2) *
        (1 + ‖p‖ ^ 2) ^ (50 : ℕ) * (W q ξ / W q v) := by
      apply mul_le_mul_of_nonneg_right _ hw
      exact mul_le_mul_of_nonneg_left (polynomial_ratio_le p ξ v h) (Real.exp_nonneg _)
    _ ≤ Real.exp (‖p‖ ^ 2 - ‖companionVelocity p ξ v‖ ^ 2) *
        (tiltConstant * Real.exp (‖p‖ ^ 2)) * (W q ξ / W q v) := by
      apply mul_le_mul_of_nonneg_right _ hw
      exact mul_le_mul_of_nonneg_left (polynomial_le_gaussian p) (Real.exp_nonneg _)
    _ = _ := by
      rw [show Real.exp (‖p‖ ^ 2 - ‖companionVelocity p ξ v‖ ^ 2) *
          (tiltConstant * Real.exp (‖p‖ ^ 2)) =
          tiltConstant * (Real.exp (‖p‖ ^ 2 - ‖companionVelocity p ξ v‖ ^ 2) *
            Real.exp (‖p‖ ^ 2)) by ring, ← Real.exp_add]
      congr 3
      ring

/-- The singular part of the transverse normalization is uniformly bounded. -/
theorem singular_fraction_le_one {r : ℝ} (hr : 0 < r) (q : ℝ) :
    r ^ (-q) / (1 + r ^ (-q)) ≤ 1 := by
  apply (div_le_one (by positivity : 0 < 1 + r ^ (-q))).mpr
  linarith

/-- Near the axis, the regular part gains the positive power `q-1`. -/
theorem regular_fraction_le_power {r : ℝ} (hr : 0 < r) (q : ℝ) :
    r⁻¹ / (1 + r ^ (-q)) ≤ r ^ (q - 1) := by
  apply (div_le_iff₀ (by positivity : 0 < 1 + r ^ (-q))).mpr
  have he : r ^ (q - 1) * r ^ (-q) = r⁻¹ := by
    rw [← Real.rpow_add hr, show (q - 1) + -q = -1 by ring, Real.rpow_neg_one]
  rw [mul_add, mul_one, he]
  linarith [Real.rpow_nonneg hr.le (q - 1)]

theorem regular_fraction_le_one {r q : ℝ} (hr : 0 < r) (hq : 1 ≤ q) :
    r⁻¹ / (1 + r ^ (-q)) ≤ 1 := by
  by_cases hr₁ : r ≤ 1
  · exact (regular_fraction_le_power hr q).trans
      (Real.rpow_le_one hr.le hr₁ (by linarith))
  · have hi : r⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (le_of_not_ge hr₁)
    apply (div_le_one (by positivity : 0 < 1 + r ^ (-q))).mpr
    linarith [Real.rpow_nonneg hr.le (-q)]

theorem inverse_weight_le_power {r : ℝ} (hr : 0 < r) (q : ℝ) :
    (1 + r ^ (-q))⁻¹ ≤ r ^ q := by
  rw [← one_div]
  apply (div_le_iff₀ (by positivity : 0 < 1 + r ^ (-q))).mpr
  have he : r ^ q * r ^ (-q) = 1 := by
    rw [← Real.rpow_add hr, add_neg_cancel, Real.rpow_zero]
  rw [mul_add, mul_one, he]
  linarith [Real.rpow_nonneg hr.le q]

/-- The shell alternative used to extract either a cold or a Gaussian tail. -/
theorem shell_alternative (p k : Velocity) {R : ℝ}
    (h : R < ‖p‖ + ‖k‖) : R / 4 < ‖p‖ ∨ R / 2 < ‖p + k‖ := by
  have he : k = (p + k) - p := by abel
  have hn : ‖k‖ ≤ ‖p + k‖ + ‖p‖ := by
    calc ‖k‖ = ‖(p + k) - p‖ := congrArg norm he
         _ ≤ ‖p + k‖ + ‖p‖ := norm_sub_le _ _
  by_cases hp : R / 4 < ‖p‖
  · exact Or.inl hp
  · exact Or.inr (by linarith)

theorem gaussian_shell_decay {w : Velocity} {R : ℝ} (hR : 0 ≤ R)
    (hw : R / 2 ≤ ‖w‖) : Real.exp (-‖w‖ ^ 2) ≤ Real.exp (-R ^ 2 / 4) := by
  apply Real.exp_le_exp.mpr
  nlinarith [norm_nonneg w]

/-- The axial exponential moment removes the tilted large-velocity tail. -/
theorem axial_tilt_tail {a u : ℝ} (hu : 0 ≤ u) (ha : u ≤ |a|) :
    Real.exp (2 * a ^ 2) ≤ Real.exp (-6 * u ^ 2) * Real.exp (8 * a ^ 2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [sq_abs a]

end BoltzmannNonuniqueness.VelocityWeight

end

end OAI
