import OAI.Geometry.CylinderCovering.Physical.CoordinateStatementDefinitions

namespace OAI

open Set MeasureTheory

noncomputable section
namespace RadialPhysical

theorem point_distance_squared (b x y t x' y' t' : ℝ) :
    ‖point b x y t - point b x' y' t'‖ ^ 2 =
      (x - x') ^ 2 + (y - y') ^ 2 + 2 * b ^ 2 * (t - t') ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [point, height, Fin.sum_univ_succ]
  have hsqrt : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  nlinarith [hsqrt]

theorem halfheight_distance {b : ℝ} (hb : 0 < b) (x y t x' y' t' : ℝ) :
    dist (canonicalPoint (2 * x / b) (2 * y / b) (2 * t - 1))
      (canonicalPoint (2 * x' / b) (2 * y' / b) (2 * t' - 1)) =
      (2 / b) * dist (point b x y t) (point b x' y' t') := by
  rw [dist_eq_norm, dist_eq_norm]
  apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, point_distance_squared, EuclideanSpace.real_norm_sq_eq]
  simp [canonicalPoint, Fin.sum_univ_succ]
  have hsqrt : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hb0 : b ≠ 0 := ne_of_gt hb
  field_simp
  rw [hsqrt]
  ring

theorem first_line_dictionary {b : ℝ} (hb : b ≠ 0) (eta x rho s : ℝ) :
    canonicalPoint (2 * x / b)
      (2 * (rho * s - eta * x * (s ^ 2 + b ^ 2) / 2) / b)
      (2 * (1 - rho + eta * x * s) - 1) =
    canonicalPoint (2 * x / b)
      ((2 * rho) * (s / b) - effectiveTilt b eta * (2 * x / b) * ((1 + (s / b) ^ 2) / 2))
      (1 - 2 * rho + effectiveTilt b eta * (2 * x / b) * (s / b)) := by
  unfold canonicalPoint effectiveTilt
  congr 1
  ext index
  fin_cases index <;> simp <;> field_simp <;> ring

theorem second_line_dictionary {b : ℝ} (hb : b ≠ 0) (eta y rho s : ℝ) :
    canonicalPoint (2 * (rho * s + eta * y * (s ^ 2 + b ^ 2) / 2) / b)
      (2 * y / b) (2 * (rho + eta * y * s) - 1) =
    canonicalPoint ((2 * rho) * (s / b) +
        effectiveTilt b eta * (2 * y / b) * ((1 + (s / b) ^ 2) / 2))
      (2 * y / b) (-1 + 2 * rho + effectiveTilt b eta * (2 * y / b) * (s / b)) := by
  unfold canonicalPoint effectiveTilt
  congr 1
  ext index
  fin_cases index <;> simp <;> field_simp <;> ring

theorem capPolynomial_angular_substitution (b beta r : ℝ) :
    capPolynomial b beta (b * r) = b ^ 4 * (canonicalProfile r + beta) / 2 := by
  unfold capPolynomial canonicalProfile
  ring

theorem linearCap_dictionary (b eta beta r : ℝ) :
    2 * linearCap b eta beta (b * r) =
      1 + effectiveTilt b eta ^ 2 * (canonicalProfile r + beta) := by
  unfold linearCap effectiveTilt
  rw [capPolynomial_angular_substitution]
  ring

theorem squareCap_dictionary (b eta beta r : ℝ) :
    2 * squareCap b eta beta (b * r) =
      Real.sqrt (1 + 2 * effectiveTilt b eta ^ 2 * (canonicalProfile r + beta)) := by
  unfold squareCap effectiveTilt
  rw [capPolynomial_angular_substitution]
  have h : 1 + 2 * (eta * b ^ 2) ^ 2 * (canonicalProfile r + beta) =
      4 * (1 / 4 + eta ^ 2 * (b ^ 4 * (canonicalProfile r + beta) / 2)) := by ring
  rw [h, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
  norm_num

theorem physical_speed_dictionary (b eta r : ℝ) :
    1 + eta ^ 2 * (((b * r) ^ 2 + b ^ 2) ^ 2 / 4 + height b ^ 2 * (b * r) ^ 2) =
      1 + effectiveTilt b eta ^ 2 * canonicalSpeed r := by
  unfold height effectiveTilt canonicalSpeed
  have hsqrt : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  simp only [mul_pow, hsqrt]
  ring

theorem scaledCost_dictionary {b : ℝ} (hb : 0 < b) (eta : ℝ) (T : ℝ → ℝ) :
    scaledCost b eta T = (b * height b / 2) *
      canonicalCost (effectiveTilt b eta) (fun r => 2 * T (b * r)) := by
  have hsub := intervalIntegral.integral_comp_mul_left
    (a := (-1 : ℝ)) (b := 1) (scaledDensity b eta T) (ne_of_gt hb)
  have hden (r : ℝ) : scaledDensity b eta T (b * r) =
      (1 / 2) * ((2 * T (b * r)) ^ 2 /
        (2 * Real.sqrt (1 + effectiveTilt b eta ^ 2 * canonicalSpeed r))) := by
    unfold scaledDensity
    rw [physical_speed_dictionary]
    ring
  simp_rw [hden] at hsub
  rw [intervalIntegral.integral_const_mul] at hsub
  simp only [mul_neg, mul_one, smul_eq_mul] at hsub
  unfold scaledCost canonicalCost
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hmul := congrArg (fun v : ℝ => b * height b * v) hsub
  have hc : b * height b * b⁻¹ = height b := by field_simp
  have hmul' : b * height b * ((1 / 2) *
      ∫ x in (-1 : ℝ)..1, (2 * T (b * x)) ^ 2 /
        (2 * Real.sqrt (1 + effectiveTilt b eta ^ 2 * canonicalSpeed x))) =
      height b * ∫ x in -b..b, scaledDensity b eta T x := by
    calc
      _ = b * height b * (b⁻¹ * ∫ x in -b..b, scaledDensity b eta T x) := hmul
      _ = _ := by rw [← mul_assoc, hc]
  nlinarith only [hmul']

theorem mapToCanonical_point {b : ℝ} (hb : b ≠ 0) (x y t : ℝ) :
    mapToCanonical b (point b x y t) =
      canonicalPoint (2 * x / b) (2 * y / b) (2 * t - 1) := by
  ext i
  fin_cases i <;> simp [mapToCanonical, point, canonicalPoint, height] <;>
    field_simp

theorem mapToCanonical_tetrahedron {b : ℝ} (hb : 0 < b) :
    mapToCanonical b '' tetrahedron b = RadialCoordinates.canonicalTetrahedron := by
  have hb0 : b ≠ 0 := ne_of_gt hb
  ext z
  constructor
  · rintro ⟨v, ⟨x, y, t, ht0, ht1, hx, hy, rfl⟩, rfl⟩
    refine ⟨2 * x / b, 2 * y / b, 2 * t - 1, by linarith, by linarith, ?_, ?_, ?_⟩
    · rw [abs_div, abs_mul, abs_of_pos hb]
      norm_num
      apply (div_le_iff₀ hb).mpr
      nlinarith
    · rw [abs_div, abs_mul, abs_of_pos hb]
      norm_num
      apply (div_le_iff₀ hb).mpr
      nlinarith
    · exact mapToCanonical_point hb0 x y t
  · rintro ⟨X, Y, Z, hZ0, hZ1, hX, hY, rfl⟩
    refine ⟨point b (b * X / 2) (b * Y / 2) ((Z + 1) / 2), ?_, ?_⟩
    · refine ⟨b * X / 2, b * Y / 2, (Z + 1) / 2,
        by linarith, by linarith, ?_, ?_, rfl⟩
      · rw [abs_div, abs_mul, abs_of_pos hb]
        norm_num
        nlinarith [mul_le_mul_of_nonneg_left hX (le_of_lt hb)]
      · rw [abs_div, abs_mul, abs_of_pos hb]
        norm_num
        nlinarith [mul_le_mul_of_nonneg_left hY (le_of_lt hb)]
    · rw [mapToCanonical_point hb0]
      ext i
      fin_cases i <;> simp [canonicalPoint] <;> field_simp
      ring

theorem scaled_table_rational_rows (tau : ℝ) :
    relativeQuadraticTerm 1 tau (1 / 120) = -tau ^ 2 / 60 ∧
    relativeQuadraticTerm (1 / 2) (tau / 2) (1 / 120) = -tau ^ 2 / 3840 ∧
    relativeQuadraticTerm (1 / 2) tau (4 / 625) = -(77 / 60000) * tau ^ 2 ∧
    relativeQuadraticTerm (1 / 2) (2 * tau) (1 / 120) = -tau ^ 2 / 240 ∧
    relativeQuadraticTerm 1 (2 * tau) (1 / 200) = -(7 / 75) * tau ^ 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    unfold relativeQuadraticTerm effectiveTilt <;> ring

theorem scaled_cap_half_edge (s : ℝ) :
    capPolynomial (1 / 2) (4 / 625) s = s ^ 4 / 4 + s ^ 2 / 16 + 1 / 5000 := by
  unfold capPolynomial
  ring

theorem scaled_table_sqrt_row (tau : ℝ) :
    relativeQuadraticTerm (1 / Real.sqrt 2) tau (1 / 125) = -(13 / 3000) * tau ^ 2 := by
  unfold relativeQuadraticTerm effectiveTilt
  have hs : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  simp only [div_pow, one_pow, hs]
  ring

theorem scaled_cap_sqrt_edge (s : ℝ) :
    capPolynomial (1 / Real.sqrt 2) (1 / 125) s = (s ^ 4 + s ^ 2 / 2) / 4 + 1 / 1000 := by
  unfold capPolynomial
  have hs : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hs4 : (Real.sqrt 2) ^ 4 = (4 : ℝ) := by nlinarith [sq_nonneg ((Real.sqrt 2) ^ 2 - 2)]
  simp only [div_pow, one_pow, hs, hs4]
  ring

theorem centered_distance {b : ℝ} (hb : 0 < b) (x y t x' y' t' : ℝ) :
    dist (canonicalPoint (x / b) (y / b) t)
      (canonicalPoint (x' / b) (y' / b) t') =
      (1 / b) * dist (point b x y t) (point b x' y' t') := by
  rw [dist_eq_norm, dist_eq_norm]
  apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, point_distance_squared, EuclideanSpace.real_norm_sq_eq]
  simp [canonicalPoint, Fin.sum_univ_succ]
  have hsqrt : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hb0 : b ≠ 0 := ne_of_gt hb
  field_simp
  rw [hsqrt]
  ring

theorem nonorthPoint_distance_squared (p q t p' q' t' : ℝ) :
    ‖nonorthPoint p q t - nonorthPoint p' q' t'‖ ^ 2 =
      (t - t') ^ 2 + ((p - p') ^ 2 + (q - q') ^ 2) / 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [nonorthPoint, Fin.sum_univ_succ]
  have hsqrt : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hs0 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  field_simp
  rw [hsqrt]
  ring

theorem nonorth_distance (p q t p' q' t' : ℝ) :
    dist (canonicalPoint p q t) (canonicalPoint p' q' t') =
      Real.sqrt 2 * dist (nonorthPoint p q t) (nonorthPoint p' q' t') := by
  rw [dist_eq_norm, dist_eq_norm]
  apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, nonorthPoint_distance_squared, EuclideanSpace.real_norm_sq_eq,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  simp [canonicalPoint, Fin.sum_univ_succ]
  have hsqrt : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  nlinarith [hsqrt]

theorem orthonormal_height_dictionary (x y z : ℝ) :
    canonicalPoint y x ((1 / Real.sqrt 2) * z) = (!₂[y, x, z] : Space) := by
  have hs0 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  ext i
  fin_cases i <;> simp [canonicalPoint]

theorem orthonormal_cubic_padding (tau H : ℝ) :
    (1 / Real.sqrt 2) * (tau ^ 2 * (1 / Real.sqrt 2) * H + 10 * tau ^ 3) =
      ((1 / Real.sqrt 2) * tau) ^ 2 * H + 20 * ((1 / Real.sqrt 2) * tau) ^ 3 := by
  have hsqrt : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hs0 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  field_simp
  linear_combination 10 * tau ^ 3 * hsqrt

theorem orthonormal_error_margin : 9 * (1 / Real.sqrt 2) ^ 2 < (20 : ℝ) := by
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem halfedge_alternative_cap (tau s : ℝ) :
    linearCap (1 / 2) (tau / 2) (1 / 120) s =
      1 / 2 + tau ^ 2 * ((1 / 2) ^ 2 * s ^ 2 *
        ((1 / 2) * (1 / 8 + s ^ 2 / 2)) + (1 / 2) ^ 3 / 1920) := by
  unfold linearCap capPolynomial
  ring

theorem halfedge_quadratic_cost (tau : ℝ) :
    quadraticCost (1 / 2) tau (4 / 625) =
      2 * height (1 / 2) * (1 / 8 - 77 / 480000 * tau ^ 2) ∧
    quadraticCost (1 / 2) (tau / 2) (1 / 120) =
      height (1 / 2) / 4 - height (1 / 2) * (1 / 2) ^ 4 / 960 * tau ^ 2 := by
  constructor <;> unfold quadraticCost relativeQuadraticTerm effectiveTilt <;> ring

theorem centeredLinearCap_dictionary (b eta beta r : ℝ) :
    centeredLinearCap b eta beta (b * r) =
      1 + effectiveTilt b eta ^ 2 * (canonicalProfile r + beta) := by
  unfold centeredLinearCap effectiveTilt canonicalProfile
  ring

theorem centered_sqrt_cap (eta s : ℝ) :
    centeredLinearCap (1 / Real.sqrt 2) eta (1 / 250) s =
      1 + eta ^ 2 * ((s ^ 4 + s ^ 2 / 2) / 2 + 1 / 1000) := by
  unfold centeredLinearCap
  have hs : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hs4 : (Real.sqrt 2) ^ 4 = (4 : ℝ) := by nlinarith [sq_nonneg ((Real.sqrt 2) ^ 2 - 2)]
  simp only [div_pow, one_pow, hs, hs4]
  ring

theorem centered_quadratic_coefficient_neg {b : ℝ} (hb : 0 < b) :
    -b / 120 + 2 * b / 1000 < 0 := by linarith

theorem centeredCost_dictionary {b : ℝ} (hb : 0 < b) (eta : ℝ) (R : ℝ → ℝ) :
    scaledCost b eta R = 2 * b * height b *
      canonicalCost (effectiveTilt b eta) (fun r => R (b * r)) := by
  rw [scaledCost_dictionary hb]
  have hscale : canonicalCost (effectiveTilt b eta) (fun r => 2 * R (b * r)) =
      4 * canonicalCost (effectiveTilt b eta) (fun r => R (b * r)) := by
    unfold canonicalCost
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro r hr
    ring
  rw [hscale]
  ring

theorem mapCenteredToCanonical_point {b : ℝ} (hb : b ≠ 0) (x y t : ℝ) :
    mapCenteredToCanonical b (point b x y t) =
      canonicalPoint (x / b) (y / b) t := by
  ext i
  fin_cases i <;> simp [mapCenteredToCanonical, point, canonicalPoint, height] <;>
    field_simp

theorem mapCenteredToCanonical_tetrahedron {b : ℝ} (hb : 0 < b) :
    mapCenteredToCanonical b '' centeredTetrahedron b = RadialCoordinates.canonicalTetrahedron := by
  have hb0 : b ≠ 0 := ne_of_gt hb
  ext z
  constructor
  · rintro ⟨v, ⟨x, y, t, ht0, ht1, hx, hy, rfl⟩, rfl⟩
    refine ⟨x / b, y / b, t, ht0, ht1, ?_, ?_, ?_⟩
    · rw [abs_div, abs_of_pos hb]
      apply (div_le_iff₀ hb).mpr
      nlinarith
    · rw [abs_div, abs_of_pos hb]
      apply (div_le_iff₀ hb).mpr
      nlinarith
    · exact mapCenteredToCanonical_point hb0 x y t
  · rintro ⟨X, Y, Z, hZ0, hZ1, hX, hY, rfl⟩
    refine ⟨point b (b * X) (b * Y) Z, ?_, ?_⟩
    · refine ⟨b * X, b * Y, Z, hZ0, hZ1, ?_, ?_, rfl⟩
      · rw [abs_mul, abs_of_pos hb]
        exact mul_le_mul_of_nonneg_left hX (le_of_lt hb)
      · rw [abs_mul, abs_of_pos hb]
        exact mul_le_mul_of_nonneg_left hY (le_of_lt hb)
    · rw [mapCenteredToCanonical_point hb0]
      ext i
      fin_cases i <;> simp [canonicalPoint] <;> field_simp

theorem centered_first_line_dictionary {b : ℝ} (hb : b ≠ 0) (eta x rho s : ℝ) :
    canonicalPoint (x / b) ((rho * s - eta * x * (s ^ 2 + b ^ 2) / 2) / b)
        (1 - rho + eta * x * s) =
      canonicalPoint (x / b)
        (rho * (s / b) - effectiveTilt b eta * (x / b) * ((1 + (s / b) ^ 2) / 2))
        (1 - rho + effectiveTilt b eta * (x / b) * (s / b)) := by
  ext i
  fin_cases i <;> simp [canonicalPoint, effectiveTilt] <;> field_simp
  ring

theorem centered_second_line_dictionary {b : ℝ} (hb : b ≠ 0) (eta y rho s : ℝ) :
    canonicalPoint ((rho * s + eta * y * (s ^ 2 + b ^ 2) / 2) / b) (y / b)
        (-1 + rho + eta * y * s) =
      canonicalPoint (rho * (s / b) +
          effectiveTilt b eta * (y / b) * ((1 + (s / b) ^ 2) / 2))
        (y / b) (-1 + rho + effectiveTilt b eta * (y / b) * (s / b)) := by
  ext i
  fin_cases i <;> simp [canonicalPoint, effectiveTilt] <;> field_simp
  ring

theorem rpow_five_halves {x : ℝ} (hx : 0 < x) :
    Real.rpow x (5 / 2) = x ^ 2 * Real.sqrt x := by
  rw [Real.rpow_eq_pow]
  rw [show (5 / 2 : ℝ) = 2 + 1 / 2 by norm_num, Real.rpow_add hx]
  rw [← Real.sqrt_eq_rpow]
  norm_num

theorem centered_fractional_padding {eta : ℝ} (heta : 0 < eta) :
    Real.rpow eta (5 / 2) = 4 * Real.sqrt 2 *
      Real.rpow (effectiveTilt (1 / Real.sqrt 2) eta) (5 / 2) := by
  have hs : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hs0 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have heff : effectiveTilt (1 / Real.sqrt 2) eta = eta / 2 := by
    unfold effectiveTilt
    rw [div_pow, hs]
    ring
  rw [heff, rpow_five_halves heta, rpow_five_halves (by positivity : 0 < eta / 2),
    Real.sqrt_div (le_of_lt heta)]
  field_simp
  norm_num

theorem physicalCoordinates_result : PhysicalCoordinatesStatement :=
  ⟨point_distance_squared,
    halfheight_distance,
    first_line_dictionary,
    second_line_dictionary,
    capPolynomial_angular_substitution,
    linearCap_dictionary,
    squareCap_dictionary,
    physical_speed_dictionary,
    scaledCost_dictionary,
    mapToCanonical_point,
    mapToCanonical_tetrahedron,
    scaled_table_rational_rows,
    scaled_cap_half_edge,
    scaled_table_sqrt_row,
    scaled_cap_sqrt_edge,
    centered_distance,
    nonorthPoint_distance_squared,
    nonorth_distance,
    orthonormal_height_dictionary,
    orthonormal_cubic_padding,
    orthonormal_error_margin,
    halfedge_alternative_cap,
    halfedge_quadratic_cost,
    centeredLinearCap_dictionary,
    centered_sqrt_cap,
    centered_quadratic_coefficient_neg,
    centeredCost_dictionary,
    mapCenteredToCanonical_point,
    mapCenteredToCanonical_tetrahedron,
    centered_first_line_dictionary,
    centered_second_line_dictionary,
    centered_fractional_padding⟩

end RadialPhysical

end

end OAI
