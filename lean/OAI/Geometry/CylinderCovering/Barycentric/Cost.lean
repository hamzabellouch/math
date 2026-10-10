import OAI.Geometry.CylinderCovering.Radial.Coordinates
import OAI.Geometry.CylinderCovering.Angular.Taylor

namespace OAI

open Set MeasureTheory

noncomputable section
namespace RadialCoordinates

theorem angular_bounds {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : |angular t| ≤ 1 := by
  rw [abs_le]
  unfold angular
  constructor <;> linarith [ht.1, ht.2]

theorem capPolynomial_angular_bounds {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    0 ≤ capPolynomial (angular t / 2) ∧ capPolynomial (angular t / 2) ≤ 501 / 1000 := by
  have hw := abs_le.mp (angular_bounds ht)
  have hsq : (angular t / 2) ^ 2 ≤ 1 / 4 := by nlinarith
  have hfour : (angular t / 2) ^ 4 ≤ 1 / 16 := by
    nlinarith [sq_nonneg (angular t / 2), sq_nonneg ((angular t / 2) ^ 2 - 1 / 4)]
  unfold capPolynomial
  constructor
  · positivity
  · linarith

theorem speedSquared_bounds {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    0 ≤ speedSquared t ∧ speedSquared t ≤ 3 := by
  have hw := abs_le.mp (angular_bounds ht)
  have hw2 : angular t ^ 2 ≤ 1 := by nlinarith
  have hG0 : 0 ≤ t ^ 2 + (1 - t) ^ 2 := by positivity
  have hG1 : t ^ 2 + (1 - t) ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr ht.2)]
  have hG2 : (t ^ 2 + (1 - t) ^ 2) ^ 2 ≤ 1 := by nlinarith
  unfold speedSquared
  constructor
  · positivity
  · linarith

private theorem density_remainder {k F E : ℝ} (hk : |k| ≤ 1 / 2)
    (hF0 : 0 ≤ F) (hF1 : F ≤ 1) (hE0 : 0 ≤ E) (hE1 : E ≤ 4) :
    |(1 / 2 + k ^ 2 * F) ^ 2 / (2 * Real.sqrt (1 + k ^ 2 * E)) -
      (1 / 8 + k ^ 2 * (F / 2 - E / 16))| ≤ (47 / 16) * k ^ 4 := by
  have hk' := abs_le.mp hk
  have hz : 4 * k ^ 2 ≤ 1 := by nlinarith
  have h := AngularTaylor.bounded_product_remainder
    (z := 4 * k ^ 2) (M := F / 4) (A := E / 4)
    (by positivity) hz (by positivity) (by linarith) (by positivity) (by linarith)
  have harg : 1 + 4 * k ^ 2 * (E / 4) = 1 + k ^ 2 * E := by ring
  rw [harg] at h
  have hid : (1 / 2 + 4 * k ^ 2 * (F / 4)) ^ 2 / Real.sqrt (1 + k ^ 2 * E) -
      (1 / 4 + 4 * k ^ 2 * (F / 4 - E / 4 / 8)) =
      2 * ((1 / 2 + k ^ 2 * F) ^ 2 / (2 * Real.sqrt (1 + k ^ 2 * E)) -
        (1 / 8 + k ^ 2 * (F / 2 - E / 16))) := by ring
  rw [hid, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at h
  nlinarith only [h]

theorem barycentric_density_remainder {k t : ℝ} (hk : |k| ≤ 1 / 2)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    |(cap k t) ^ 2 / (2 * Real.sqrt (1 + k ^ 2 * speedSquared t)) -
      (1 / 8 + k ^ 2 * (capPolynomial (angular t / 2) / 2 - speedSquared t / 16))| ≤
      (47 / 16) * k ^ 4 := by
  have hF := capPolynomial_angular_bounds ht
  have hE := speedSquared_bounds ht
  exact density_remainder hk hF.1 (by linarith [hF.2]) hE.1 (by linarith [hE.2])

theorem continuous_barycentric_density (k : ℝ) :
    Continuous (fun t : ℝ => (cap k t) ^ 2 /
      (2 * Real.sqrt (1 + k ^ 2 * speedSquared t))) := by
  apply Continuous.div
  · unfold cap capPolynomial angular
    fun_prop
  · unfold speedSquared angular
    fun_prop
  · intro t
    have hE : 0 ≤ speedSquared t := by unfold speedSquared; positivity
    have hpos : 0 < 1 + k ^ 2 * speedSquared t := by positivity
    exact mul_ne_zero (by norm_num) (ne_of_gt (Real.sqrt_pos.2 hpos))

theorem barycentric_reference_integral (k : ℝ) :
    (∫ t in (0 : ℝ)..1,
      (1 / 8 + k ^ 2 * (capPolynomial (angular t / 2) / 2 - speedSquared t / 16))) =
      1 / 8 - (11 / 3000) * k ^ 2 := by
  rw [intervalIntegral.integral_add (continuous_const.intervalIntegrable _ _)
    (by apply Continuous.intervalIntegrable; unfold capPolynomial speedSquared angular; fun_prop)]
  rw [intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    barycentric_quadratic_coefficient_integral]
  norm_num
  ring

theorem J_expansion {k : ℝ} (hk : |k| ≤ 1 / 2) :
    |J k / Real.sqrt 2 - (1 / 8 - (11 / 3000) * k ^ 2)| ≤ (47 / 16) * k ^ 4 := by
  have hsqrt : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  rw [J, mul_div_cancel_left₀ _ hsqrt]
  rw [← barycentric_reference_integral k]
  rw [← intervalIntegral.integral_sub
    ((continuous_barycentric_density k).intervalIntegrable _ _)
    (by apply Continuous.intervalIntegrable; unfold capPolynomial speedSquared angular; fun_prop)]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := (47 / 16) * k ^ 4)
    (f := fun t : ℝ => (cap k t) ^ 2 / (2 * Real.sqrt (1 + k ^ 2 * speedSquared t)) -
      (1 / 8 + k ^ 2 * (capPolynomial (angular t / 2) / 2 - speedSquared t / 16)))
    (fun t ht => by
      rw [Real.norm_eq_abs]
      have hti : t ∈ Ioc (0 : ℝ) 1 := by simpa using ht
      exact barycentric_density_remainder hk ⟨le_of_lt hti.1, hti.2⟩)
  simpa [Real.norm_eq_abs] using h

theorem J_strict_half_target {k : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1 / 5000) :
    2 * J k < Real.sqrt 2 / 4 := by
  have hk : |k| ≤ 1 / 2 := by rw [abs_of_pos hk0]; linarith
  have h := (abs_le.mp (J_expansion hk)).2
  have hk2 : k ^ 2 ≤ (1 / 5000 : ℝ) ^ 2 := by nlinarith
  have hstrict : (47 / 16 : ℝ) * k ^ 4 < (11 / 3000 : ℝ) * k ^ 2 := by
    have hp : 0 < k ^ 2 := sq_pos_of_pos hk0
    nlinarith [mul_nonneg (sq_nonneg k) (sub_nonneg.mpr hk2)]
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hratio : J k / Real.sqrt 2 < 1 / 8 := by linarith
  have hJ : J k < (1 / 8) * Real.sqrt 2 := (div_lt_iff₀ hsqrt).mp hratio
  linarith

theorem J_canonical_cost_identity (k : ℝ) :
    2 * J k = (Real.sqrt 2 / 4) *
      (∫ r in (-1 : ℝ)..1,
        (1 + k ^ 2 * ((r ^ 2 + r ^ 4) / 2 + 1 / 500)) ^ 2 /
          (2 * Real.sqrt (1 + k ^ 2 * (2 * r ^ 2 + ((1 + r ^ 2) / 2) ^ 2)))) := by
  let f : ℝ → ℝ := fun r =>
    (1 + k ^ 2 * ((r ^ 2 + r ^ 4) / 2 + 1 / 500)) ^ 2 /
      (2 * Real.sqrt (1 + k ^ 2 * (2 * r ^ 2 + ((1 + r ^ 2) / 2) ^ 2)))
  have hsub := intervalIntegral.integral_comp_mul_add
    (a := (0 : ℝ)) (b := 1) f (by norm_num : (2 : ℝ) ≠ 0) (-1)
  norm_num only [mul_zero, zero_add, mul_one, add_neg_cancel,
    show (2 : ℝ) + -1 = 1 by norm_num, smul_eq_mul] at hsub
  have hf (t : ℝ) : f (2 * t + -1) =
      4 * ((cap k t) ^ 2 / (2 * Real.sqrt (1 + k ^ 2 * speedSquared t))) := by
    have hR : 1 + k ^ 2 * (((2 * t + -1) ^ 2 + (2 * t + -1) ^ 4) / 2 + 1 / 500) =
        2 * cap k t := by unfold cap capPolynomial angular; ring
    have hE : 2 * (2 * t + -1) ^ 2 + ((1 + (2 * t + -1) ^ 2) / 2) ^ 2 =
        speedSquared t := by unfold speedSquared angular; ring
    dsimp [f]
    rw [hR, hE]
    ring
  simp_rw [hf] at hsub
  rw [intervalIntegral.integral_const_mul] at hsub
  change 2 * J k = (Real.sqrt 2 / 4) * (∫ r in (-1 : ℝ)..1, f r)
  unfold J
  linear_combination (Real.sqrt 2 / 2) * hsub

end RadialCoordinates

end

end OAI
