import OAI.Geometry.CylinderCovering.Radial.CoordinatesDefinitions
import OAI.Geometry.CylinderCovering.Barycentric.Radial

namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace

noncomputable section
namespace RadialCoordinates

theorem barycentricPoint_sum (s q p : ℝ) :
    ∑ i, barycentricPoint s q p i = 1 := by
  simp [barycentricPoint, Fin.sum_univ_succ]
  ring

theorem barycentricPoint_mem_iff (s q p : ℝ) :
    barycentricPoint s q p ∈ barycentricSimplex ↔
      0 ≤ s ∧ s ≤ 1 ∧ |q| ≤ s ∧ |p| ≤ 1 - s := by
  simp only [barycentricSimplex, mem_ofPred_eq, barycentricPoint_sum, and_true]
  simp only [barycentricPoint, Fin.forall_fin_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Matrix.cons_val_fin_one, Fin.forall_fin_zero, and_true]
  rw [abs_le, abs_le]
  constructor
  · rintro ⟨ha, hb, hc, hd⟩
    constructor
    · linarith
    constructor
    · linarith
    constructor <;> constructor <;> linarith
  · rintro ⟨hs, hs', ⟨hq, hq'⟩, ⟨hp, hp'⟩⟩
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem barycentricPoint_reconstruct {v : BarycentricSpace}
    (hv : ∑ i, v i = 1) :
    barycentricPoint (v 0 + v 1) (v 0 - v 1) (v 2 - v 3) = v := by
  have hv' : v 0 + v 1 + v 2 + v 3 = 1 := by
    simpa [Fin.sum_univ_succ, add_assoc] using hv
  ext i
  fin_cases i <;> simp [barycentricPoint] <;> linarith

theorem barycentricPoint_distance_squared (s q p s' q' p' : ℝ) :
    ‖barycentricPoint s q p - barycentricPoint s' q' p'‖ ^ 2 =
      (s - s') ^ 2 + ((q - q') ^ 2 + (p - p') ^ 2) / 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [barycentricPoint, Fin.sum_univ_succ]
  ring

theorem canonicalPoint_distance_squared (s q p s' q' p' : ℝ) :
    ‖canonicalPoint s q p - canonicalPoint s' q' p'‖ ^ 2 =
      8 * ‖barycentricPoint s q p - barycentricPoint s' q' p'‖ ^ 2 := by
  rw [barycentricPoint_distance_squared, EuclideanSpace.real_norm_sq_eq]
  simp [canonicalPoint, Fin.sum_univ_succ]
  have hsqrt : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  nlinarith [hsqrt]

theorem canonicalPoint_distance (s q p s' q' p' : ℝ) :
    dist (canonicalPoint s q p) (canonicalPoint s' q' p') =
      (2 * Real.sqrt 2) * dist (barycentricPoint s q p) (barycentricPoint s' q' p') := by
  rw [dist_eq_norm, dist_eq_norm]
  apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [canonicalPoint_distance_squared]
  simp only [mul_pow]
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

theorem canonicalPoint_mem_of_simplex {s q p : ℝ}
    (h : barycentricPoint s q p ∈ barycentricSimplex) :
    canonicalPoint s q p ∈ canonicalTetrahedron := by
  obtain ⟨hs, hs', hq, hp⟩ := (barycentricPoint_mem_iff s q p).mp h
  refine ⟨2 * q, 2 * p, 2 * s - 1, by linarith, by linarith, ?_, ?_, rfl⟩
  · rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith
  · rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith

theorem exists_positive_radial_representation {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (k p : ℝ) :
    ∃ t S : ℝ, 0 < t ∧ t < 1 ∧ 0 < S ∧
      a = S * t + k * p * t ^ 2 ∧
      b = S * (1 - t) - k * p * (1 - t) ^ 2 := by
  obtain ⟨t, S, ht, hS, ha', hb', _, _⟩ :=
    CylinderCovering.BarycentricRadial.exists_positive_radial_representation ha hb (k * p)
  exact ⟨t, S, ht.1, ht.2, hS, ha', hb'⟩

theorem radial_representation_sum_difference {a b S t k p : ℝ}
    (ha : a = S * t + k * p * t ^ 2)
    (hb : b = S * (1 - t) - k * p * (1 - t) ^ 2) :
    a + b = S + k * p * angular t ∧
    a - b = S * angular t + k * p * (1 + angular t ^ 2) / 2 := by
  rw [ha, hb]
  constructor <;> unfold angular <;> ring

theorem interior_complementary_representations {a b c d : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hsum : a + b + c + d = 1) (k : ℝ) :
    ∃ t r S T : ℝ,
      0 < t ∧ t < 1 ∧ 0 < r ∧ r < 1 ∧ 0 < S ∧ 0 < T ∧
      a = S * t + k * (c - d) * t ^ 2 ∧
      b = S * (1 - t) - k * (c - d) * (1 - t) ^ 2 ∧
      c = T * r - k * (a - b) * r ^ 2 ∧
      d = T * (1 - r) + k * (a - b) * (1 - r) ^ 2 ∧
      1 = S + T + k * (c - d) * angular t - k * (a - b) * angular r ∧
      a - b = S * angular t + k * (c - d) * (1 + angular t ^ 2) / 2 ∧
      c - d = T * angular r - k * (a - b) * (1 + angular r ^ 2) / 2 := by
  obtain ⟨t, S, ht0, ht1, hS, hat, hbt⟩ :=
    exists_positive_radial_representation ha hb k (c - d)
  obtain ⟨r, T, hr0, hr1, hT, hcr, hdr⟩ :=
    exists_positive_radial_representation hc hd (-k) (a - b)
  have heq1 := radial_representation_sum_difference hat hbt
  have heq2 := radial_representation_sum_difference hcr hdr
  refine ⟨t, r, S, T, ht0, ht1, hr0, hr1, hS, hT, hat, hbt, ?_, ?_, ?_, heq1.2, ?_⟩
  · nlinarith [hcr]
  · nlinarith [hdr]
  · nlinarith [heq1.1, heq2.1]
  · nlinarith [heq2.2]

theorem velocity_quadratic_identity (t c : ℝ) :
    velocity t - velocity c =
      (2 * (t - c)) • ray t - ((t - c) ^ 2) • (!₂[1, -1] : Plane) := by
  ext i
  fin_cases i <;> simp [velocity, ray] <;> ring

theorem cap_obstruction_identity (p q : ℝ) :
    capPolynomial p + capPolynomial q - (p ^ 2 + q ^ 2 + 8 * p ^ 2 * q ^ 2) =
      4 * (p ^ 2 - q ^ 2) ^ 2 + 2 / 1000 := by
  unfold capPolynomial
  ring

theorem cap_obstruction_positive (p q : ℝ) :
    0 < capPolynomial p + capPolynomial q -
      (p ^ 2 + q ^ 2 + 8 * p ^ 2 * q ^ 2) := by
  rw [cap_obstruction_identity]
  positivity

theorem capPolynomial_angular_expansion (t : ℝ) :
    capPolynomial (angular t / 2) =
      4 * t ^ 4 + (-8) * t ^ 3 + 7 * t ^ 2 + (-3) * t + 501 / 1000 := by
  unfold capPolynomial angular
  ring

theorem speedSquared_expansion (t : ℝ) :
    speedSquared t = 4 * t ^ 4 + (-8) * t ^ 3 + 16 * t ^ 2 + (-12) * t + 3 := by
  unfold speedSquared angular
  ring

private theorem integral_quartic (a b c d e : ℝ) :
    (∫ t in (0 : ℝ)..1, a * t ^ 4 + b * t ^ 3 + c * t ^ 2 + d * t + e) =
      a / 5 + b / 4 + c / 3 + d / 2 + e := by
  repeat' rw [intervalIntegral.integral_add
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  simp only [intervalIntegral.integral_const_mul, integral_pow,
    intervalIntegral.integral_const]
  rw [intervalIntegral.integral_const_mul d (fun t : ℝ => t), integral_id]
  norm_num
  ring

theorem capPolynomial_integral :
    (∫ t in (0 : ℝ)..1, capPolynomial (angular t / 2)) = 2 / 15 + 1 / 1000 := by
  simp_rw [capPolynomial_angular_expansion]
  rw [integral_quartic]
  norm_num

theorem speedSquared_integral :
    (∫ t in (0 : ℝ)..1, speedSquared t) = 17 / 15 := by
  simp_rw [speedSquared_expansion]
  rw [integral_quartic]
  norm_num

theorem barycentric_quadratic_coefficient_integral :
    (∫ t in (0 : ℝ)..1,
      capPolynomial (angular t / 2) / 2 - speedSquared t / 16) = -11 / 3000 := by
  rw [intervalIntegral.integral_sub
    (by apply Continuous.intervalIntegrable; unfold capPolynomial angular; fun_prop)
    (by apply Continuous.intervalIntegrable; unfold speedSquared angular; fun_prop)]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_div,
    capPolynomial_integral, speedSquared_integral]
  norm_num

theorem frozen_intercept_identity (S k p t c : ℝ) :
    S • ray t + (k * p) • (velocity t - velocity c) =
      (S + 2 * k * p * (t - c)) • ray t -
        (k * p * (t - c) ^ 2) • (!₂[1, -1] : Plane) := by
  ext i
  fin_cases i <;> simp [velocity, ray] <;> ring

theorem transverse_unit_norm : ‖(!₂[1, -1] : Plane)‖ = Real.sqrt 2 := by
  apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num [Fin.sum_univ_succ]

theorem frozen_intercept_remainder (S k p t c : ℝ) :
    ‖S • ray t + (k * p) • (velocity t - velocity c) -
      (S + 2 * k * p * (t - c)) • ray t‖ =
      Real.sqrt 2 * |k| * |p| * (t - c) ^ 2 := by
  rw [frozen_intercept_identity]
  have heq (A B : Plane) : (A - B) - A = -B := by abel
  rw [heq, norm_neg, norm_smul, transverse_unit_norm, Real.norm_eq_abs,
    abs_mul, abs_mul, abs_sq]
  ring

theorem frozen_intercept_enclosure {S k p t c M ell : ℝ}
    (hk : 0 ≤ k) (hp : |p| ≤ 1) (hell : 0 ≤ ell) (ht : |t - c| ≤ ell)
    (hS : 0 ≤ S) (hSM : S ≤ M) :
    ∃ rho : ℝ, -2 * k * ell ≤ rho ∧ rho ≤ M + 2 * k * ell ∧
      ‖S • ray t + (k * p) • (velocity t - velocity c) - rho • ray t‖ ≤
        Real.sqrt 2 * k * ell ^ 2 := by
  have hpdt : |p * (t - c)| ≤ ell := by
    rw [abs_mul]
    exact (mul_le_mul hp ht (abs_nonneg _) (by norm_num)).trans (by simp)
  have hb := abs_le.mp hpdt
  refine ⟨S + 2 * k * p * (t - c), ?_, ?_, ?_⟩
  · nlinarith [mul_nonneg hk (show 0 ≤ p * (t - c) + ell by linarith)]
  · nlinarith [mul_nonneg hk (show 0 ≤ ell - p * (t - c) by linarith)]
  · rw [frozen_intercept_remainder, abs_of_nonneg hk]
    have hsq : (t - c) ^ 2 ≤ ell ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (t - c)) hell).mpr ht
    have hprod : |p| * (t - c) ^ 2 ≤ ell ^ 2 :=
      (mul_le_mul_of_nonneg_right hp (sq_nonneg _)).trans (by simpa using hsq)
    nlinarith [mul_nonneg (show 0 ≤ Real.sqrt 2 * k by positivity)
      (sub_nonneg.mpr hprod)]

end RadialCoordinates

end

end OAI
