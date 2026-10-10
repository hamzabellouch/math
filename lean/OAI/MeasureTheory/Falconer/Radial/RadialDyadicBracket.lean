import OAI.MeasureTheory.Falconer.Radial.RadialScaleIntersection
import Mathlib.Algebra.Order.Archimedean.Basic

namespace OAI

/-! # Selecting a retained dyadic scale for an arbitrary cap radius -/

namespace Falconer

theorem radial_dyadic_bracket (N : ℕ) {r : ℝ}
    (hr : ((2:ℝ)^N)⁻¹ ≤ r) (hr1 : r ≤ 1) :
    ∃ j ≤ N, r ≤ ((2:ℝ)^j)⁻¹ ∧ ((2:ℝ)^j)⁻¹ < 2*r := by
  have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr
  obtain ⟨j,hlo,hhi⟩ := exists_nat_pow_near_of_lt_one hr0 hr1
    (by norm_num : (0:ℝ) < 1/2) (by norm_num : (1/2:ℝ) < 1)
  have he : (1/2:ℝ)^j = ((2:ℝ)^j)⁻¹ := by rw [one_div,inv_pow]
  rw [he] at hhi
  have hj : j ≤ N := by
    by_contra h
    have hp : (2:ℝ)^N < (2:ℝ)^j := pow_lt_pow_right₀ (by norm_num) (by omega)
    have hi : ((2:ℝ)^j)⁻¹ < ((2:ℝ)^N)⁻¹ :=
      (inv_lt_inv₀ (by positivity) (by positivity)).mpr hp
    exact (not_lt_of_ge hr) (hhi.trans_lt hi)
  refine ⟨j,hj,hhi,?_⟩
  rw [pow_succ,he] at hlo
  linarith

theorem radial_dyadic_bracket_above (N B : ℕ) {r : ℝ}
    (hr : ((2:ℝ)^N)⁻¹ ≤ r) (hrB : r ≤ ((2:ℝ)^B)⁻¹) :
    ∃ j, B ≤ j ∧ j ≤ N ∧ r ≤ ((2:ℝ)^j)⁻¹ ∧ ((2:ℝ)^j)⁻¹ < 2*r := by
  have hr1 : r ≤ 1 := hrB.trans (inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num)))
  obtain ⟨j,hj,hhi,hlo⟩ := radial_dyadic_bracket N hr hr1
  have hBj : B ≤ j := by
    by_contra h
    have hp : (2:ℝ)^(j+1) ≤ (2:ℝ)^B := pow_le_pow_right₀ (by norm_num) (by omega)
    have hinv : ((2:ℝ)^B)⁻¹ ≤ ((2:ℝ)^(j+1))⁻¹ := inv_anti₀ (by positivity) hp
    have he : ((2:ℝ)^(j+1))⁻¹ = ((2:ℝ)^j)⁻¹/2 := by rw [pow_succ,mul_inv_rev]; ring
    rw [he] at hinv
    linarith
  exact ⟨j,hBj,hj,hhi,hlo⟩

end Falconer

end OAI
