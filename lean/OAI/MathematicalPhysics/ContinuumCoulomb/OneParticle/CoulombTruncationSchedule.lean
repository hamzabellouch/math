import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedCoulombBox

namespace OAI

/-! Explicit polynomial cap and box schedules. The single natural guard
is fixed by the fixed one-well density; it is not an input or an oracle. -/

noncomputable section
namespace ContinuumCoulomb.CoulombTruncationSchedule

def guard (freq : ℝ) : ℕ := Nat.ceil (max 1
  (max (2 * Real.pi * localizedAmplitudeBound freq ^ 2)
    (2 * localizedDensitySecondMoment freq))) + 1

def scale (P : ℕ) : ℕ := 8 * (P + 1)
def radius (freq : ℝ) (P : ℕ) : ℕ := guard freq * scale P ^ 2
def epsilon (freq : ℝ) (P : ℕ) : ℚ := 1 / ((guard freq : ℚ) * (scale P : ℚ))

theorem guard_one_le (freq : ℝ) : 1 ≤ (guard freq : ℝ) := by
  have hc := Nat.le_ceil (max 1 (max (2 * Real.pi * localizedAmplitudeBound freq ^ 2)
    (2 * localizedDensitySecondMoment freq)))
  have h := (le_max_left (1 : ℝ) _).trans hc
  simp only [guard, Nat.cast_add, Nat.cast_one]
  linarith

theorem guard_cap (freq : ℝ) :
    2 * Real.pi * localizedAmplitudeBound freq ^ 2 ≤ (guard freq : ℝ) := by
  have hc := Nat.le_ceil (max 1 (max (2 * Real.pi * localizedAmplitudeBound freq ^ 2)
    (2 * localizedDensitySecondMoment freq)))
  have h := (le_max_left (2 * Real.pi * localizedAmplitudeBound freq ^ 2)
    (2 * localizedDensitySecondMoment freq)).trans ((le_max_right (1 : ℝ) _).trans hc)
  simp only [guard, Nat.cast_add, Nat.cast_one]
  linarith

theorem guard_tail (freq : ℝ) :
    2 * localizedDensitySecondMoment freq ≤ (guard freq : ℝ) := by
  have hc := Nat.le_ceil (max 1 (max (2 * Real.pi * localizedAmplitudeBound freq ^ 2)
    (2 * localizedDensitySecondMoment freq)))
  have h := (le_max_right (2 * Real.pi * localizedAmplitudeBound freq ^ 2)
    (2 * localizedDensitySecondMoment freq)).trans ((le_max_right (1 : ℝ) _).trans hc)
  simp only [guard, Nat.cast_add, Nat.cast_one]
  linarith

theorem scale_eight_le (P : ℕ) : (8 : ℝ) ≤ scale P := by
  simp only [scale, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
  linarith [show (0 : ℝ) ≤ P from Nat.cast_nonneg _]

theorem epsilon_positive (freq : ℝ) (P : ℕ) : 0 < (epsilon freq P : ℝ) := by
  have hg := guard_one_le freq
  have hs := scale_eight_le P
  simp only [epsilon, Rat.cast_div, Rat.cast_one, Rat.cast_mul, Rat.cast_natCast]
  positivity

theorem radius_positive (freq : ℝ) (P : ℕ) : 0 < (radius freq P : ℝ) := by
  have hg := guard_one_le freq
  have hs := scale_eight_le P
  simp only [radius, Nat.cast_mul, Nat.cast_pow]
  positivity

theorem scalar_budget {C S B M : ℝ} (hC : 1 ≤ C) (hS : 1 ≤ S)
    (hB : B ≤ C) (hM : 2 * M ≤ C) :
    B * (1 / (C * S)) ^ 2 + 2 * (1 / (C * S))⁻¹ * M / (C * S ^ 2) ^ 2 ≤
      2 / S ^ 2 := by
  have hC0 : 0 < C := by linarith
  have hS0 : 0 < S := by linarith
  have hcap : B * (1 / (C * S)) ^ 2 ≤ 1 / S ^ 2 := by
    calc
      _ ≤ C * (1 / (C * S)) ^ 2 := mul_le_mul_of_nonneg_right hB (sq_nonneg _)
      _ = C⁻¹ * (1 / S ^ 2) := by field_simp [hC0.ne', hS0.ne']
      _ ≤ 1 / S ^ 2 := mul_le_of_le_one_left (by positivity)
        ((inv_le_one₀ hC0).mpr hC)
  have htail : 2 * (1 / (C * S))⁻¹ * M / (C * S ^ 2) ^ 2 ≤ 1 / S ^ 2 := by
    calc
      _ = (2 * M) * (C * S) / (C * S ^ 2) ^ 2 := by field_simp [hC0.ne', hS0.ne']
      _ ≤ C * (C * S) / (C * S ^ 2) ^ 2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hM (by positivity)) (by positivity)
      _ = (1 / S ^ 2) * S⁻¹ := by field_simp [hC0.ne', hS0.ne']
      _ ≤ 1 / S ^ 2 := mul_le_of_le_one_right (by positivity) ((inv_le_one₀ hS0).mpr hS)
  calc
    _ ≤ 1 / S ^ 2 + 1 / S ^ 2 := add_le_add hcap htail
    _ = _ := by ring

theorem error {freq : ℝ} (hfreq : 0 < freq) (P : ℕ) (u : PlanarPosition) :
    |localizedCoulombProfileAt freq u -
      localizedCoulombBoxIntegral freq (epsilon freq P : ℝ) (radius freq P : ℝ) u| ≤
      (4 * ((P : ℝ) + 1))⁻¹ := by
  have h := localizedCoulombProfile_box_error hfreq (epsilon_positive freq P)
    (radius_positive freq P) u
  have hg := guard_one_le freq
  have hs := scale_eight_le P
  have hb := scalar_budget hg (by linarith : (1 : ℝ) ≤ scale P)
    (guard_cap freq) (guard_tail freq)
  have hcast : (epsilon freq P : ℝ) = 1 / ((guard freq : ℝ) * (scale P : ℝ)) := by
    simp only [epsilon, Rat.cast_div, Rat.cast_one, Rat.cast_mul, Rat.cast_natCast]
  rw [hcast] at h
  simp only [radius, Nat.cast_mul, Nat.cast_pow] at h
  rw [hcast]
  simp only [radius, Nat.cast_mul, Nat.cast_pow]
  apply (h.trans hb).trans
  have hP : 1 ≤ (P : ℝ) + 1 := by linarith [show (0 : ℝ) ≤ P from Nat.cast_nonneg _]
  simp only [scale, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
  calc
    2 / (8 * ((P : ℝ) + 1)) ^ 2 =
        (4 * ((P : ℝ) + 1))⁻¹ * (8 * ((P : ℝ) + 1))⁻¹ := by
      field_simp
      ring
    _ ≤ _ := mul_le_of_le_one_right (by positivity)
      ((inv_le_one₀ (by positivity)).mpr (by linarith))

end ContinuumCoulomb.CoulombTruncationSchedule

end

end OAI
