import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ResolventNumericalBounds

namespace OAI

/-! The explicit rational machine approximates the actual planar
resolvent to inverse-polynomial accuracy. No numerical oracle occurs in
the statement or the program. -/

noncomputable section
namespace ContinuumCoulomb.ResolventSchedule

theorem scheduled_error_bound (x : Input)
    (hR : ‖PlanarForcingProgram.position x.2‖ ≤ (x.1.1 : ℝ)) :
    RationalHeatBox.resolventErrorBound (argument x) ≤ 4 * (scale x.1.2 : ℝ)⁻¹ := by
  let r := PlanarForcingProgram.position x.2
  let R := (x.1.1 : ℝ)
  let Q := (scale x.1.2 : ℝ)
  let N := (count x.1.1 x.1.2 : ℝ)
  let w := Q - Q⁻¹
  let e := (2 ^ precision x.1.2 : ℝ)⁻¹
  have hQnat : 1 ≤ scale x.1.2 := Nat.succ_le_iff.mpr (scale_positive x.1.2)
  have hQ : 1 ≤ Q := by
    dsimp only [Q]
    exact_mod_cast hQnat
  have hQ0 : 0 < Q := by linarith
  have hA : 1 ≤ R + 3 := by
    have hR0 : 0 ≤ R := Nat.cast_nonneg _
    linarith
  have hN : N = 4096 * (R + 3) ^ 4 * Q ^ 8 := by
    dsimp only [N, R, Q, count, countPrefix]
    push_cast
    rfl
  have hw0 : 0 ≤ w := by
    have hi : Q⁻¹ ≤ 1 := (inv_le_one₀ hQ0).mpr hQ
    dsimp only [w]
    linarith
  have hw : w ≤ Q := by
    have hi : 0 ≤ Q⁻¹ := by positivity
    dsimp only [w]
    linarith
  have he0 : 0 ≤ e := by dsimp only [e]; positivity
  have he : Q ^ 2 * e ≤ Q⁻¹ := taylor_precision_bound (scale x.1.2) hQnat
  have h := scalar_error_bound hA hQ hN hw0 hw
    (time_constant_bound r hR hQ) (spatial_constant_bound r hR hQ) he0 he
  have hid : RationalHeatBox.resolventErrorBound (argument x) =
      N * (4 * planarBoxTimeConstant r Q⁻¹ * (w / N) ^ 2 + (w / N) *
        (4 * (2 * planarBoxSpatialConstant r Q⁻¹ * (2 / N) +
          (e + 8 / N) / (4 * Q⁻¹)))) + Q⁻¹ + Real.exp (-Q) := by
    rw [RationalHeatBox.resolventErrorBound, argument_endpoint]
    simp only [argument, RationalHeatBox.planeErrorBound, RationalHeatBox.spatialStep,
      Rat.cast_inv, Rat.cast_natCast, Rat.cast_div, Rat.cast_sub, Rat.cast_ofNat]
    rfl
  rw [hid]
  exact h

theorem approximation_error (x : Input)
    (hR : ‖PlanarForcingProgram.position x.2‖ ≤ (x.1.1 : ℝ)) :
    |(approximate x : ℝ) - planarResolventMode (PlanarForcingProgram.position x.2)| ≤
      ((x.1.2 : ℝ) + 1)⁻¹ := by
  let r := PlanarForcingProgram.position x.2
  have hQ : (0 : ℝ) < scale x.1.2 := by exact_mod_cast scale_positive x.1.2
  have hM : (RationalHeatBox.timeEndpoint (argument x) : ℝ) +
      (‖PlanarForcingProgram.position (argument x).2.1.2.1‖ + 2) ^ 2 /
        (4 * ((argument x).2.2.1 : ℝ)) ≤ (argument x).2.1.1.1 := by
    rw [argument_endpoint]
    simp only [argument, Rat.cast_inv, Rat.cast_natCast, magnitude, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_add, Nat.cast_ofNat]
    exact magnitude_bound r hR hQ
  have h := RationalHeatBox.resolvent_error (argument x) (argument_start_positive x)
    (argument_step_nonnegative x) (count_positive x.1.1 x.1.2) (count_positive x.1.1 x.1.2) hM
  have h' := h.trans (scheduled_error_bound x hR)
  have hlast : 4 * (scale x.1.2 : ℝ)⁻¹ ≤ ((x.1.2 : ℝ) + 1)⁻¹ := by
    have hp : (0 : ℝ) < (x.1.2 : ℝ) + 1 := by positivity
    simp only [scale, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    apply (mul_le_mul_iff_left₀ hp).mp
    field_simp
    norm_num
  exact h'.trans hlast

end ContinuumCoulomb.ResolventSchedule

end

end OAI
