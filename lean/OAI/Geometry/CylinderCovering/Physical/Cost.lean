import OAI.Geometry.CylinderCovering.Physical.CostDefinitions
import OAI.Geometry.CylinderCovering.Physical.UnitEdgeFootprints
import OAI.Geometry.CylinderCovering.Angular.Taylor

namespace OAI

open Set MeasureTheory

noncomputable section
namespace CylinderCovering.UnitEdgeFootprints

private def capPolynomial (s : ℝ) : ℝ := s ^ 2 / 4 + s ^ 4 + 1 / 960
private def directionPolynomial (s : ℝ) : ℝ := (1 / 4 + s ^ 2) ^ 2 + 2 * s ^ 2
private def density (η s : ℝ) : ℝ :=
  (1 / 4 + η ^ 2 * capPolynomial s) /
    Real.sqrt (1 + η ^ 2 * directionPolynomial s)
private def quadraticDensity (η s : ℝ) : ℝ :=
  1 / 4 + η ^ 2 * (capPolynomial s - directionPolynomial s / 8)

private lemma polynomial_bounds {s : ℝ} (hs : s ∈ Icc (-1 / 2 : ℝ) (1 / 2)) :
    0 ≤ capPolynomial s ∧ capPolynomial s ≤ 1 / 4 ∧
    0 ≤ directionPolynomial s ∧ directionPolynomial s ≤ 1 := by
  have hs2 : s ^ 2 ≤ 1 / 4 := by nlinarith [hs.1, hs.2]
  have hs4 : s ^ 4 ≤ 1 / 16 := by nlinarith [sq_nonneg (s ^ 2 - 1 / 4)]
  unfold capPolynomial directionPolynomial
  constructor
  · positivity
  constructor
  · nlinarith
  constructor
  · positivity
  · nlinarith [sq_nonneg s]

private lemma local_remainder {z P A : ℝ}
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (hP0 : 0 ≤ P) (hP1 : P ≤ 1 / 4)
    (hA0 : 0 ≤ A) (hA1 : A ≤ 1) :
    |(1 / 4 + z * P) / Real.sqrt (1 + z * A) -
      (1 / 4 + z * (P - A / 8))| ≤ z ^ 2 := by
  let B : ℝ := 1 / 4 + z * P
  let R : ℝ := 1 / Real.sqrt (1 + z * A) - (1 - z * A / 2)
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hB1 : B ≤ 1 / 2 := by
    have hp := mul_le_mul hz1 hP1 hP0 (by norm_num : (0 : ℝ) ≤ 1)
    dsimp [B]
    nlinarith only [hp]
  have hA2 : A ^ 2 ≤ 1 := by nlinarith only [hA0, hA1]
  have hR : |R| ≤ (3 / 8) * z ^ 2 := by
    have h := AngularTaylor.inv_sqrt_remainder (mul_nonneg hz0 hA0)
    have hb := mul_le_of_le_one_right (sq_nonneg z) hA2
    dsimp [R]
    nlinarith only [h, hb]
  have hBR : |B * R| ≤ (3 / 16) * z ^ 2 := by
    rw [abs_mul, abs_of_nonneg hB0]
    have h := mul_le_mul hB1 hR (abs_nonneg R) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    nlinarith only [h]
  have hPA0 : 0 ≤ P * A := mul_nonneg hP0 hA0
  have hPA1 : P * A ≤ 1 / 4 := by
    nlinarith only [mul_le_mul hP1 hA1 hA0 (by norm_num : (0 : ℝ) ≤ 1 / 4)]
  have hZPA : |z ^ 2 * (P * A / 2)| ≤ (1 / 8) * z ^ 2 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_nonneg (by positivity : 0 ≤ P * A / 2)]
    nlinarith only [mul_le_mul_of_nonneg_left hPA1 (sq_nonneg z)]
  have heq : (1 / 4 + z * P) / Real.sqrt (1 + z * A) -
      (1 / 4 + z * (P - A / 8)) = B * R - z ^ 2 * (P * A / 2) := by
    dsimp [B, R]
    ring
  rw [heq]
  have h : |B * R - z ^ 2 * (P * A / 2)| ≤ |B * R| + |z ^ 2 * (P * A / 2)| := by
    simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (B * R) 0 (z ^ 2 * (P * A / 2))
  nlinarith only [h, hBR, hZPA, sq_nonneg z]

private lemma density_remainder {η s : ℝ} (hη : |η| ≤ 1)
    (hs : s ∈ Icc (-1 / 2 : ℝ) (1 / 2)) :
    |density η s - quadraticDensity η s| ≤ η ^ 4 := by
  obtain ⟨hP0, hP1, hA0, hA1⟩ := polynomial_bounds hs
  have hz1 : η ^ 2 ≤ 1 := by rw [abs_le] at hη; nlinarith [hη.1, hη.2]
  have h := local_remainder (sq_nonneg η) hz1 hP0 hP1 hA0 hA1
  simpa only [density, quadraticDensity, ← pow_mul, show (2 * 2 : ℕ) = 4 by decide] using h

private lemma sourceCap_sq (η s : ℝ) :
    sourceCap η s ^ 2 = 1 / 4 + η ^ 2 * capPolynomial s := by
  unfold sourceCap capPolynomial
  exact Real.sq_sqrt (by positivity)

private lemma density_continuous (η : ℝ) : Continuous (density η) := by
  unfold density capPolynomial directionPolynomial
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro s
  apply ne_of_gt
  apply Real.sqrt_pos.mpr
  positivity

private lemma quadraticDensity_continuous (η : ℝ) : Continuous (quadraticDensity η) := by
  unfold quadraticDensity capPolynomial directionPolynomial
  fun_prop

private lemma quadraticDensity_integral (η : ℝ) :
    (∫ s in (-1 / 2 : ℝ)..(1 / 2), quadraticDensity η s) = 1 / 4 - η ^ 2 / 960 := by
  have heq : quadraticDensity η = fun s : ℝ =>
      (1 / 4 + η ^ 2 * (1 / 960 - 1 / 128)) +
        (-η ^ 2 / 16) * s ^ 2 + (7 * η ^ 2 / 8) * s ^ 4 := by
    funext s
    unfold quadraticDensity capPolynomial directionPolynomial
    ring
  rw [heq, intervalIntegral.integral_add
    ((by fun_prop : Continuous (fun s : ℝ =>
      (1 / 4 + η ^ 2 * (1 / 960 - 1 / 128)) + (-η ^ 2 / 16) * s ^ 2)).intervalIntegrable _ _)
    ((by fun_prop : Continuous (fun s : ℝ => (7 * η ^ 2 / 8) * s ^ 4)).intervalIntegrable _ _),
    intervalIntegral.integral_add intervalIntegrable_const
      ((by fun_prop : Continuous (fun s : ℝ => (-η ^ 2 / 16) * s ^ 2)).intervalIntegrable _ _),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_pow, integral_pow]
  norm_num
  ring

theorem source_cost_remainder {η : ℝ} (hη : |η| ≤ 1) :
    |2 * limitingArea η (sourceCap η) - height * (1 / 4 - η ^ 2 / 960)| ≤
      height * η ^ 4 := by
  have hlim : 2 * limitingArea η (sourceCap η) =
      height * ∫ s in (-1 / 2 : ℝ)..(1 / 2), density η s := by
    unfold limitingArea
    rw [mul_left_comm (2 : ℝ) height]
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    apply intervalIntegral.integral_congr
    intro s _
    dsimp only
    rw [sourceCap_sq]
    unfold density directionPolynomial
    ring
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (-1 / 2 : ℝ)) (b := (1 / 2 : ℝ)) (C := η ^ 4)
    (f := fun s => density η s - quadraticDensity η s) (by
      intro s hs
      rw [Real.norm_eq_abs]
      apply density_remainder hη
      rw [Set.uIoc_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 1 / 2)] at hs
      exact ⟨hs.1.le, hs.2⟩)
  rw [intervalIntegral.integral_sub (density_continuous η |>.intervalIntegrable _ _)
    (quadraticDensity_continuous η |>.intervalIntegrable _ _), quadraticDensity_integral] at hb
  norm_num only [Real.norm_eq_abs, show |(1 / 2 : ℝ) - -1 / 2| = 1 by norm_num, mul_one] at hb
  rw [hlim, ← mul_sub, abs_mul, abs_of_pos height_pos]
  simpa only [neg_div] using mul_le_mul_of_nonneg_left hb height_pos.le

theorem source_cost_strict {η : ℝ} (hη : 0 < η) (hsmall : η ≤ 1 / 40) :
    2 * limitingArea η (sourceCap η) < height / 4 := by
  have hb : |η| ≤ 1 := by rw [abs_of_pos hη]; linarith
  have h := (abs_le.mp (source_cost_remainder hb)).2
  have hz : η ^ 2 ≤ 1 / 1600 := by nlinarith
  have hz4 : η ^ 4 ≤ η ^ 2 / 1600 := by
    nlinarith only [mul_nonneg (sq_nonneg η) (sub_nonneg.mpr hz)]
  have hh := mul_le_mul_of_nonneg_left hz4 height_pos.le
  have hp := mul_pos height_pos (sq_pos_of_pos hη)
  nlinarith only [h, hh, hp]

theorem source_cost : SourceCostStatement :=
  ⟨fun _ hη => source_cost_remainder hη, fun _ hη hsmall => source_cost_strict hη hsmall⟩

end CylinderCovering.UnitEdgeFootprints

end

end OAI
