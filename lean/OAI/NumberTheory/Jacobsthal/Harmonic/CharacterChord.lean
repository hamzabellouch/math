import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

namespace OAI

namespace Erdos970

section

open scoped BigOperators
namespace ErdosHyperbolaFourier

noncomputable def characterProgression (N : ℕ) [NeZero N]
    (start step : ZMod N) (J : ℕ) : ℂ :=
  ∑ j ∈ Finset.range J, ZMod.stdAddChar (start + (j : ZMod N)*step)

theorem characterProgression_factor (N : ℕ) [NeZero N]
    (start step : ZMod N) (J : ℕ) :
    characterProgression N start step J =
      ZMod.stdAddChar start * ∑ j ∈ Finset.range J, (ZMod.stdAddChar step)^j := by
  unfold characterProgression
  simp only [AddChar.map_add_eq_mul, ← nsmul_eq_mul, AddChar.map_nsmul_eq_pow,
    Finset.mul_sum]

theorem characterProgression_zero_length (N : ℕ) [NeZero N] (start step : ZMod N) :
    characterProgression N start step 0 = 0 := by simp [characterProgression]

theorem characterProgression_zero_step (N : ℕ) [NeZero N] (start : ZMod N) (J : ℕ) :
    characterProgression N start 0 J = (J : ℂ) * ZMod.stdAddChar start := by
  simp [characterProgression]

theorem norm_characterProgression_zero_step (N : ℕ) [NeZero N]
    (start : ZMod N) (J : ℕ) : ‖characterProgression N start 0 J‖ = J := by
  rw [characterProgression_zero_step, norm_mul]
  simp [AddChar.norm_apply]

theorem norm_geom_mul_sub_le_two (z : ℂ) (hz : ‖z‖ = 1) (J : ℕ) :
    ‖∑ j ∈ Finset.range J, z^j‖ * ‖1-z‖ ≤ 2 := by
  rw [← norm_mul, geom_sum_mul_neg]
  calc
    _ ≤ ‖(1 : ℂ)‖ + ‖z^J‖ := norm_sub_le _ _
    _ = 2 := by norm_num [norm_pow, hz]

theorem norm_characterProgression_mul_chord (N : ℕ) [NeZero N]
    (start step : ZMod N) (J : ℕ) :
    ‖characterProgression N start step J‖ * ‖1-ZMod.stdAddChar step‖ ≤ 2 := by
  rw [characterProgression_factor, norm_mul, AddChar.norm_apply, one_mul]
  exact norm_geom_mul_sub_le_two _ (AddChar.norm_apply _ _) J

end ErdosHyperbolaFourier

end

section

namespace ErdosHyperbolaFourier

def cyclicDistance (N : ℕ) (step : ZMod N) : ℕ := min step.val (N-step.val)

theorem cyclicDistance_pos (N : ℕ) [NeZero N] (step : ZMod N) (hs : step ≠ 0) :
    0 < cyclicDistance N step := by
  have hv : 0 < step.val := Nat.pos_of_ne_zero (fun hv => hs ((ZMod.val_eq_zero step).mp hv))
  exact lt_min hv (Nat.sub_pos_of_lt step.val_lt)

private theorem sine_half_lower (x : ℝ) (hx : 0 ≤ x) (hxhalf : x ≤ 1/2) :
    2*x ≤ Real.sin (Real.pi*x) := by
  have ht : Real.pi*x ≤ Real.pi/2 := by nlinarith [Real.pi_pos]
  have h := Real.mul_le_sin (mul_nonneg Real.pi_pos.le hx) ht
  calc
    _ = (2/Real.pi)*(Real.pi*x) := by field_simp
    _ ≤ _ := h

theorem sine_distance_lower (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    2*min x (1-x) ≤ Real.sin (Real.pi*x) := by
  by_cases hh : x ≤ 1/2
  · rw [min_eq_left (by linarith)]
    exact sine_half_lower x hx hh
  · rw [min_eq_right (by linarith)]
    have h := sine_half_lower (1-x) (by linarith) (by linarith)
    have he : Real.pi*(1-x) = Real.pi-Real.pi*x := by ring
    simpa only [he, Real.sin_pi_sub] using h

theorem exponential_chord_lower (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    4*min x (1-x) ≤ ‖Complex.exp (Complex.I * ((2*Real.pi*x : ℝ) : ℂ))-1‖ := by
  have hs := sine_distance_lower x hx hx1
  have hs0 : 0 ≤ Real.sin (Real.pi*x) :=
    (mul_nonneg (by norm_num) (le_min hx (sub_nonneg.mpr hx1))).trans hs
  rw [Complex.norm_exp_I_mul_ofReal_sub_one,
    show (2*Real.pi*x)/2 = Real.pi*x by ring, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (by norm_num) hs0)]
  nlinarith

theorem standard_character_chord_lower (N : ℕ) [NeZero N] (step : ZMod N) :
    4*(cyclicDistance N step : ℝ)/(N : ℝ) ≤ ‖1-ZMod.stdAddChar step‖ := by
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hv : (step.val : ℝ) ≤ N := by exact_mod_cast step.val_lt.le
  have he : ZMod.stdAddChar step =
      Complex.exp (Complex.I * ((2*Real.pi*((step.val : ℝ)/N) : ℝ) : ℂ)) := by
    rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
    congr 1
    push_cast
    ring
  have h := exponential_chord_lower ((step.val : ℝ)/N) (by positivity)
    ((div_le_one hN).mpr hv)
  have hsub : ((N-step.val : ℕ) : ℝ) = (N : ℝ)-step.val := by
    exact Nat.cast_sub step.val_lt.le
  have hmin : min ((step.val : ℝ)/N) (1-(step.val : ℝ)/N) =
      (cyclicDistance N step : ℝ)/(N : ℝ) := by
    rw [show 1-(step.val : ℝ)/N = ((N : ℝ)-step.val)/N by field_simp,
      min_div_div_right hN.le]
    simp only [cyclicDistance, Nat.cast_min, hsub]
  rw [hmin] at h
  rw [he, norm_sub_rev]
  convert h using 1; ring

end ErdosHyperbolaFourier

end

end Erdos970

end OAI
