import Mathlib.Analysis.Complex.JensenFormula
import OAI.NumberTheory.Ostmann.Characters.CharacterMellinBound

namespace OAI

/-! # Local zero counts for primitive character L-functions

Jensen's formula is applied to disks centered on Re(s)=2.  The larger
radius stays in the positive half-plane; the smaller disk covers a unit
ordinate interval in the right half of the critical strip.
-/

namespace Ostmann

open Metric Set MeromorphicOn
open scoped BigOperators

noncomputable def characterZeroCenter (t : ℝ) : ℂ := 2 + (t : ℂ) * Complex.I

@[simp] theorem characterZeroCenter_re (t : ℝ) : (characterZeroCenter t).re = 2 := by
  simp [characterZeroCenter]

@[simp] theorem characterZeroCenter_im (t : ℝ) : (characterZeroCenter t).im = t := by
  simp [characterZeroCenter]

theorem characterZeroCenter_norm (t : ℝ) : ‖characterZeroCenter t‖ ≤ 2 + |t| := by
  simpa using Complex.norm_le_abs_re_add_abs_im (characterZeroCenter t)

theorem character_disk_re (t : ℝ) (z : ℂ)
    (hz : z ∈ closedBall (characterZeroCenter t) (7 / 4 : ℝ)) : 1 / 4 ≤ z.re := by
  rw [mem_closedBall, dist_eq_norm] at hz
  have hr := (Complex.abs_re_le_norm (z - characterZeroCenter t)).trans hz
  simp only [Complex.sub_re, characterZeroCenter_re] at hr
  linarith [(abs_le.mp hr).1]

theorem character_disk_norm (t : ℝ) (z : ℂ)
    (hz : z ∈ closedBall (characterZeroCenter t) (7 / 4 : ℝ)) : ‖z‖ ≤ |t| + 4 := by
  rw [mem_closedBall, dist_eq_norm] at hz
  have htri := norm_add_le (z - characterZeroCenter t) (characterZeroCenter t)
  rw [sub_add_cancel] at htri
  linarith [characterZeroCenter_norm t]

theorem PrimitiveComplexCharacter.L_disk_bound (χ : PrimitiveComplexCharacter)
    (t : ℝ) (z : ℂ) (hz : z ∈ closedBall (characterZeroCenter t) (7 / 4 : ℝ)) :
    ‖χ.L z‖ ≤ 16 * (χ.modulus : ℝ) * (|t| + 2) := by
  have hr := character_disk_re t z hz
  have hnorm := character_disk_norm t z hz
  have hq : (1 : ℝ) ≤ χ.modulus := by exact_mod_cast χ.positive
  calc
    _ ≤ ‖z‖ * ((χ.modulus : ℝ) + 1) / z.re := χ.L_norm_bound_positive z (by linarith)
    _ ≤ ‖z‖ * ((χ.modulus : ℝ) + 1) / (1 / 4) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hr
    _ ≤ (|t| + 4) * ((χ.modulus : ℝ) + 1) / (1 / 4) := by gcongr
    _ ≤ _ := by
      norm_num only [div_eq_mul_inv, inv_div, inv_one]
      nlinarith [abs_nonneg t, mul_nonneg (sub_nonneg.mpr hq) (abs_nonneg t)]

noncomputable def characterLocalZeroMass (χ : PrimitiveComplexCharacter) (t : ℝ) : ℤ :=
  ∑ᶠ z, divisor χ.L (closedBall (characterZeroCenter t) (13 / 8 : ℝ)) z

/-- A logarithmic zero count, including analytic multiplicity, on each local disk. -/
theorem PrimitiveComplexCharacter.local_zero_mass_bound (χ : PrimitiveComplexCharacter)
    (t : ℝ) :
    (characterLocalZeroMass χ t : ℝ) ≤
      Real.log (48 * (χ.modulus : ℝ) * (|t| + 2)) / Real.log (14 / 13) := by
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  have hq : (1 : ℝ) ≤ χ.modulus := by exact_mod_cast χ.positive
  have ha : AnalyticOnNhd ℂ χ.L (closedBall (characterZeroCenter t) |(7 / 4 : ℝ)|) :=
    fun _ _ => (DirichletCharacter.differentiable_LFunction χ.nontrivial).analyticAt _
  have hlo := χ.L_lower_re_two (characterZeroCenter t) (characterZeroCenter_re t)
  have hne : χ.L (characterZeroCenter t) ≠ 0 := by
    intro he
    rw [he, norm_zero] at hlo
    linarith
  have hM : 1 ≤ 16 * (χ.modulus : ℝ) * (|t| + 2) := by
    nlinarith [abs_nonneg t, mul_nonneg (sub_nonneg.mpr hq) (abs_nonneg t)]
  have hj := ha.sum_divisor_le (r := (13 / 8 : ℝ)) (R := (7 / 4 : ℝ))
    (by norm_num) (by norm_num) hM hne (fun z hz =>
      χ.L_disk_bound t z (by simpa only [abs_of_pos (by norm_num : (0 : ℝ) < 7 / 4)] using
        sphere_subset_closedBall hz))
  have hratio : (16 * (χ.modulus : ℝ) * (|t| + 2)) / ‖χ.L (characterZeroCenter t)‖ ≤
      48 * (χ.modulus : ℝ) * (|t| + 2) := by
    apply (div_le_iff₀ (by linarith : 0 < ‖χ.L (characterZeroCenter t)‖)).2
    nlinarith [mul_le_mul_of_nonneg_left hlo
      (show 0 ≤ 48 * (χ.modulus : ℝ) * (|t| + 2) by positivity)]
  have hlog : 0 < Real.log (14 / 13 : ℝ) := Real.log_pos (by norm_num)
  have hlogratio := Real.log_le_log (div_pos (by positivity)
    (by linarith : 0 < ‖χ.L (characterZeroCenter t)‖)) hratio
  rw [show |(13 / 8 : ℝ)| = 13 / 8 by norm_num,
    show (7 / 4 : ℝ) / (13 / 8) = 14 / 13 by norm_num] at hj
  exact hj.trans (div_le_div_of_nonneg_right hlogratio hlog.le)

end Ostmann

end OAI
