import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.RationalResolventError
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ResolventSchedule

namespace OAI

/-! Elementary quantitative bounds for the fixed polynomial schedule.
These estimates keep all mesh choices explicit. -/

noncomputable section
namespace ContinuumCoulomb.ResolventSchedule

theorem succ_le_two_pow (n : ℕ) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ]
    omega

theorem taylor_precision_bound (Q : ℕ) (hQ : 1 ≤ Q) :
    (Q : ℝ) ^ 2 * (2 ^ (4 * Q) : ℝ)⁻¹ ≤ (Q : ℝ)⁻¹ := by
  have hn : Q ^ 3 ≤ 2 ^ (4 * Q) := by
    calc
      Q ^ 3 ≤ Q ^ 4 := pow_le_pow_right₀ hQ (by norm_num)
      _ ≤ (Q + 1) ^ 4 := Nat.pow_le_pow_left (by omega) 4
      _ ≤ (2 ^ Q) ^ 4 := Nat.pow_le_pow_left (succ_le_two_pow Q) 4
      _ = 2 ^ (4 * Q) := by rw [← pow_mul]; congr 1; omega
  have hQr : (0 : ℝ) < Q := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hQ)
  have hnr : (Q : ℝ) ^ 3 ≤ 2 ^ (4 * Q) := by exact_mod_cast hn
  have hp : (0 : ℝ) < 2 ^ (4 * Q) := by positivity
  apply (mul_le_mul_iff_left₀ hQr).mp
  rw [inv_mul_cancel₀ hQr.ne']
  calc
    (Q : ℝ) ^ 2 * (2 ^ (4 * Q) : ℝ)⁻¹ * Q = Q ^ 3 / (2 ^ (4 * Q) : ℝ) := by ring
    _ ≤ 1 := (div_le_one hp).mpr hnr

theorem exp_tail_le_inverse {Q : ℝ} (hQ : 0 < Q) : Real.exp (-Q) ≤ Q⁻¹ := by
  rw [Real.exp_neg]
  exact inv_anti₀ hQ (by linarith [Real.add_one_le_exp Q])

theorem mesh_fraction_bound {A Q : ℝ} (hA : 1 ≤ A) (hQ : 1 ≤ Q) :
    (4 * A ^ 2 * Q ^ 5 + 192 * A * Q ^ 3 + 8 * Q ^ 2) /
      (4096 * A ^ 4 * Q ^ 8) ≤ Q⁻¹ := by
  have hA0 : 0 < A := by linarith
  have hQ0 : 0 < Q := by linarith
  have hN : 0 < 4096 * A ^ 4 * Q ^ 8 := by positivity
  have h₂ : A ^ 2 * Q ^ 6 ≤ A ^ 4 * Q ^ 8 :=
    mul_le_mul (pow_le_pow_right₀ hA (by norm_num)) (pow_le_pow_right₀ hQ (by norm_num))
      (by positivity) (by positivity)
  have h₁ : A * Q ^ 4 ≤ A ^ 4 * Q ^ 8 := by
    have ha : A ≤ A ^ 4 := by simpa using pow_le_pow_right₀ hA (show 1 ≤ 4 by norm_num)
    exact mul_le_mul ha (pow_le_pow_right₀ hQ (by norm_num)) (by positivity) (by positivity)
  have h₀ : Q ^ 3 ≤ A ^ 4 * Q ^ 8 := by
    calc
      Q ^ 3 ≤ Q ^ 8 := pow_le_pow_right₀ hQ (by norm_num)
      _ ≤ A ^ 4 * Q ^ 8 := le_mul_of_one_le_left (by positivity) (one_le_pow₀ hA)
  have hn : (4 * A ^ 2 * Q ^ 5 + 192 * A * Q ^ 3 + 8 * Q ^ 2) * Q ≤
      4096 * A ^ 4 * Q ^ 8 := by
    calc
      _ = 4 * (A ^ 2 * Q ^ 6) + 192 * (A * Q ^ 4) + 8 * Q ^ 3 := by ring
      _ ≤ 204 * (A ^ 4 * Q ^ 8) := by linarith
      _ ≤ _ := by nlinarith [show 0 ≤ A ^ 4 * Q ^ 8 by positivity]
  calc
    _ ≤ ((4096 * A ^ 4 * Q ^ 8) / Q) / (4096 * A ^ 4 * Q ^ 8) :=
      div_le_div_of_nonneg_right ((le_div_iff₀ hQ0).mpr hn) hN.le
    _ = Q⁻¹ := by field_simp

theorem spatial_constant_bound (r : PlanarPosition) {R Q : ℝ}
    (hR : ‖r‖ ≤ R) (hQ : 1 ≤ Q) :
    planarBoxSpatialConstant r Q⁻¹ ≤ 12 * (R + 3) * Q ^ 2 := by
  have hR0 : 0 ≤ R := (norm_nonneg r).trans hR
  have hQsq : Q ≤ Q ^ 2 := by nlinarith
  have hmain := mul_le_mul_of_nonneg_right (show 2 * (‖r‖ + 2) ≤ 2 * (R + 2) by linarith)
    (sq_nonneg Q)
  have hnonneg := mul_nonneg hR0 (sq_nonneg Q)
  simp only [planarBoxSpatialConstant, inv_inv, inv_pow, div_inv_eq_mul]
  nlinarith

theorem time_constant_bound (r : PlanarPosition) {R Q : ℝ}
    (hR : ‖r‖ ≤ R) (hQ : 1 ≤ Q) :
    planarBoxTimeConstant r Q⁻¹ ≤ (R + 3) ^ 2 * Q ^ 3 := by
  have hR0 : 0 ≤ R := (norm_nonneg r).trans hR
  have hQ0 : 0 ≤ Q := by linarith
  have hQ2 : Q ^ 2 ≤ Q ^ 3 := by nlinarith
  have hQ1 : Q ≤ Q ^ 3 := by nlinarith
  have hsquare : (‖r‖ + 2) ^ 2 ≤ (R + 2) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mpr (by linarith)
  have hc : 2 + (‖r‖ + 2) ^ 2 / 4 ≤ (R + 3) ^ 2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hc (show 0 ≤ Q ^ 3 by positivity)
  have hQne : Q ≠ 0 := by linarith
  have heq : planarBoxTimeConstant r Q⁻¹ =
      Q ^ 2 + Q + (‖r‖ + 2) ^ 2 * Q ^ 3 / 4 := by
    unfold planarBoxTimeConstant
    field_simp [hQne]
    ring
  rw [heq]
  nlinarith

theorem scalar_error_bound {A Q N w Lt Ls e : ℝ}
    (hA : 1 ≤ A) (hQ : 1 ≤ Q) (hN : N = 4096 * A ^ 4 * Q ^ 8)
    (hw0 : 0 ≤ w) (hw : w ≤ Q)
    (hLt : Lt ≤ A ^ 2 * Q ^ 3) (hLs : Ls ≤ 12 * A * Q ^ 2)
    (he0 : 0 ≤ e) (he : Q ^ 2 * e ≤ Q⁻¹) :
    N * (4 * Lt * (w / N) ^ 2 + (w / N) *
      (4 * (2 * Ls * (2 / N) + (e + 8 / N) / (4 * Q⁻¹)))) +
      Q⁻¹ + Real.exp (-Q) ≤ 4 * Q⁻¹ := by
  have hQ0 : 0 < Q := by linarith
  have hA0 : 0 < A := by linarith
  have hN0 : 0 < N := by rw [hN]; positivity
  have hw2 : w ^ 2 ≤ Q ^ 2 := (sq_le_sq₀ hw0 hQ0.le).mpr hw
  have h₁ := mul_le_mul hLt hw2 (sq_nonneg w) (show 0 ≤ A ^ 2 * Q ^ 3 by positivity)
  have h₂ := mul_le_mul hLs hw hw0 (show 0 ≤ 12 * A * Q ^ 2 by positivity)
  have h₃ := mul_le_mul_of_nonneg_left hw hQ0.le
  have hnum : 4 * Lt * w ^ 2 + 16 * Ls * w + 8 * Q * w ≤
      4 * A ^ 2 * Q ^ 5 + 192 * A * Q ^ 3 + 8 * Q ^ 2 := by
    nlinarith
  have hmesh : (4 * Lt * w ^ 2 + 16 * Ls * w + 8 * Q * w) / N ≤ Q⁻¹ := by
    apply (div_le_div_of_nonneg_right hnum hN0.le).trans
    rw [hN]
    exact mesh_fraction_bound hA hQ
  have hsample : Q * w * e ≤ Q⁻¹ :=
    (mul_le_mul_of_nonneg_right (show Q * w ≤ Q ^ 2 by nlinarith [h₃]) he0).trans he
  have hid : N * (4 * Lt * (w / N) ^ 2 + (w / N) *
      (4 * (2 * Ls * (2 / N) + (e + 8 / N) / (4 * Q⁻¹)))) =
      (4 * Lt * w ^ 2 + 16 * Ls * w + 8 * Q * w) / N + Q * w * e := by
    field_simp [hN0.ne', hQ0.ne']
    ring
  rw [hid]
  linarith [exp_tail_le_inverse hQ0]

theorem argument_endpoint (x : Input) :
    RationalHeatBox.timeEndpoint (argument x) = (scale x.1.2 : ℚ) := by
  have hN : (count x.1.1 x.1.2 : ℚ) ≠ 0 := by
    exact_mod_cast (count_positive x.1.1 x.1.2).ne'
  have hQ : (scale x.1.2 : ℚ) ≠ 0 := by
    exact_mod_cast (scale_positive x.1.2).ne'
  change (scale x.1.2 : ℚ)⁻¹ + (count x.1.1 x.1.2 : ℚ) *
    (((scale x.1.2 : ℚ) - (scale x.1.2 : ℚ)⁻¹) / count x.1.1 x.1.2) = _
  field_simp [hN, hQ]
  ring

theorem argument_start_positive (x : Input) : 0 < ((argument x).2.2.1 : ℝ) := by
  have hQ := scale_positive x.1.2
  change 0 < (((scale x.1.2 : ℚ)⁻¹ : ℚ) : ℝ)
  rw [Rat.cast_inv, Rat.cast_natCast]
  positivity

theorem argument_step_nonnegative (x : Input) : 0 ≤ ((argument x).2.2.2 : ℝ) := by
  have hQ : (1 : ℚ) ≤ scale x.1.2 := by
    exact_mod_cast (Nat.succ_le_iff.mpr (scale_positive x.1.2))
  have hN : (0 : ℚ) < count x.1.1 x.1.2 := by exact_mod_cast count_positive x.1.1 x.1.2
  have hi : (scale x.1.2 : ℚ)⁻¹ ≤ 1 := (inv_le_one₀ (by linarith)).mpr hQ
  have hh : 0 ≤ ((scale x.1.2 : ℚ) - (scale x.1.2 : ℚ)⁻¹) / count x.1.1 x.1.2 :=
    div_nonneg (by linarith) hN.le
  exact_mod_cast hh

theorem magnitude_bound (r : PlanarPosition) {R Q : ℝ}
    (hR : ‖r‖ ≤ R) (hQ : 0 < Q) :
    Q + (‖r‖ + 2) ^ 2 / (4 * Q⁻¹) ≤ (R + 3) ^ 2 * Q := by
  have hR0 : 0 ≤ R := (norm_nonneg r).trans hR
  have hsquare : (‖r‖ + 2) ^ 2 ≤ (R + 2) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mpr (by linarith)
  have hc : 1 + (‖r‖ + 2) ^ 2 / 4 ≤ (R + 3) ^ 2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hc hQ.le
  have hid : Q + (‖r‖ + 2) ^ 2 / (4 * Q⁻¹) =
      (1 + (‖r‖ + 2) ^ 2 / 4) * Q := by field_simp [hQ.ne']
  rw [hid]
  exact hm

end ContinuumCoulomb.ResolventSchedule

end

end OAI
