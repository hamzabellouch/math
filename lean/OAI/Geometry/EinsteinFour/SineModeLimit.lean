import OAI.Geometry.EinsteinFour.ScalarDirichlet
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! The first scalar Dirichlet eigenvalue and its radial comparison limit. -/

namespace PositiveEinsteinFour.Jacobi

open Filter Topology

noncomputable section

theorem two_sub_two_cos (x : ℝ) : 2 - 2 * Real.cos x = 4 * Real.sin (x / 2) ^ 2 := by
  have hc := Real.cos_two_mul (x / 2)
  have hs := Real.sin_sq_add_cos_sq (x / 2)
  rw [show 2 * (x / 2) = x by ring] at hc
  nlinarith

def firstEigenvalue (t : ℝ) (N : ℕ) : ℝ :=
  2 - (t / (N + 1)) ^ 2 - 2 * Real.cos (firstSineAngle N)

def scaledFirstEigenvalue (t : ℝ) (N : ℕ) : ℝ :=
  ((N : ℝ) + 1) ^ 2 * firstEigenvalue t N

theorem scaledFirstEigenvalue_eq_sinc (t : ℝ) (N : ℕ) :
    scaledFirstEigenvalue t N =
      Real.pi ^ 2 * Real.sinc (Real.pi / (2 * (N + 1))) ^ 2 - t ^ 2 := by
  have hN : (N : ℝ) + 1 ≠ 0 := by positivity
  have hx : Real.pi / (2 * ((N : ℝ) + 1)) ≠ 0 := by positivity
  rw [Real.sinc_of_ne_zero hx]
  unfold scaledFirstEigenvalue firstEigenvalue firstSineAngle
  rw [show 2 - (t / ((N : ℝ) + 1)) ^ 2 -
      2 * Real.cos (Real.pi / (N + 1)) =
      (2 - 2 * Real.cos (Real.pi / (N + 1))) - (t / (N + 1)) ^ 2 by ring,
    two_sub_two_cos]
  have hh : Real.pi / ((N : ℝ) + 1) / 2 = Real.pi / (2 * (N + 1)) := by field_simp
  rw [hh]
  field_simp
  ring

theorem scaledFirstEigenvalue_tendsto (t : ℝ) :
    Tendsto (scaledFirstEigenvalue t) atTop (𝓝 (Real.pi ^ 2 - t ^ 2)) := by
  have hzero : Tendsto (fun N : ℕ => Real.pi / (2 * ((N : ℝ) + 1)))
      atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (Real.pi / 2)
    convert h using 1
    · funext N
      field_simp
    · simp
  have hs : Tendsto (fun N : ℕ => Real.sinc (Real.pi / (2 * ((N : ℝ) + 1))))
      atTop (𝓝 1) := by
    simpa only [Function.comp_def, Real.sinc_zero] using
      Real.continuous_sinc.continuousAt.tendsto.comp hzero
  convert ((hs.pow 2).const_mul (Real.pi ^ 2)).sub_const (t ^ 2) using 1
  · funext N
    exact scaledFirstEigenvalue_eq_sinc t N
  · simp

theorem firstEigenvalue_eventually_pos {t : ℝ} (ht : 0 ≤ t) (htπ : t < Real.pi) :
    ∀ᶠ N : ℕ in atTop, 0 < firstEigenvalue t N := by
  have hlim : 0 < Real.pi ^ 2 - t ^ 2 := by nlinarith [Real.pi_pos]
  filter_upwards [(scaledFirstEigenvalue_tendsto t).eventually (eventually_gt_nhds hlim)] with N hN
  have hsq : 0 < ((N : ℝ) + 1) ^ 2 := by positivity
  exact (mul_pos_iff_of_pos_left hsq).mp hN

theorem first_mode_coefficient_tendsto {t : ℝ} (ht : 0 ≤ t) (htπ : t < Real.pi) :
    Tendsto (fun N : ℕ => (t / (N + 1)) ^ 2 / firstEigenvalue t N)
      atTop (𝓝 (t ^ 2 / (Real.pi ^ 2 - t ^ 2))) := by
  have hne : Real.pi ^ 2 - t ^ 2 ≠ 0 := by nlinarith [Real.pi_pos]
  have h := (tendsto_const_nhds (x := t ^ 2)).div (scaledFirstEigenvalue_tendsto t) hne
  convert h using 1
  funext N
  unfold scaledFirstEigenvalue
  simp only [div_pow, div_div]
  rfl

end

end PositiveEinsteinFour.Jacobi

end OAI
