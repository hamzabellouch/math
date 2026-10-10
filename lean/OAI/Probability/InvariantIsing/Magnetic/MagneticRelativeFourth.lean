import OAI.Probability.InvariantIsing.Magnetic.MagneticFourthCumulant

namespace OAI

/-! A relative fourth-derivative bound, uniform in the spatial bias.
The centered fourth cumulant costs only one spin variance. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma magnetic_relative_centered_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {M Q A : ℝ → ℝ} (hM : Measurable M) (hQ : Measurable Q) (hA : Measurable A)
    (bM : ∀ x, |M x| ≤ 1) {B C : ℝ} (bQ : ∀ x, |Q x| ≤ B)
    (bA : ∀ x, |A x| ≤ C * Q x) :
    |(∫ x, A x * M x ∂μ) - (∫ x, A x ∂μ) * (∫ x, M x ∂μ)| ≤
      2 * C * ∫ x, Q x ∂μ := by
  let m := ∫ x, M x ∂μ
  have hiQ : Integrable Q μ := Integrable.of_bound hQ.aestronglyMeasurable B
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using bQ x)
  have hiA : Integrable A μ := (hiQ.const_mul C).mono' hA.aestronglyMeasurable
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using bA x)
  have hiAM : Integrable (fun x => A x * M x) μ := hiA.mul_bdd hM.aestronglyMeasurable
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using bM x)
  have he : (∫ x, A x * M x ∂μ) - (∫ x, A x ∂μ) * m =
      ∫ x, A x * (M x - m) ∂μ := by
    rw [show (fun x => A x * (M x - m)) = fun x => A x * M x - A x * m by
      funext x; ring, integral_sub hiAM (hiA.mul_const m), integral_mul_const]
  have hi : Integrable (fun x => A x * (M x - m)) μ := by
    convert hiAM.sub (hiA.mul_const m) using 1
    funext x
    change A x * (M x - m) = A x * M x - A x * m
    ring
  change |(∫ x, A x * M x ∂μ) - (∫ x, A x ∂μ) * m| ≤ _
  rw [he]
  calc
    _ ≤ ∫ x, |A x * (M x - m)| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, (2 * C) * Q x ∂μ := by
      apply integral_mono hi.abs (hiQ.const_mul _)
      intro x
      change |A x * (M x - m)| ≤ 2 * C * Q x
      rw [abs_mul]
      calc
        _ ≤ |A x| * 2 := mul_le_mul_of_nonneg_left
          (magnetic_centered_spin_bound μ bM x) (abs_nonneg _)
        _ ≤ (C * Q x) * 2 := mul_le_mul_of_nonneg_right (bA x) (by norm_num)
        _ = _ := by ring
    _ = _ := integral_const_mul _ _

private lemma magnetic_abs_five (a b c d e : ℝ) :
    |a + b + c + d + e| ≤ |a| + |b| + |c| + |d| + |e| := by
  have h1 := abs_add_le a b
  have h2 := abs_add_le (a + b) c
  have h3 := abs_add_le (a + b + c) d
  have h4 := abs_add_le (a + b + c + d) e
  linarith

theorem fieldFourthTransform_relative_bound {ζ : ℝ} (hζ : 0 ≤ ζ) (v : ℝ≥0)
    {F M Q R S : ℝ → ℝ} (hF : Measurable F) (hG : HasLinearGrowth F)
    (hM : Measurable M) (hQ : Measurable Q) (hR : Measurable R) (hS : Measurable S)
    (bM : ∀ x, |M x| ≤ 1) (hQpos : ∀ x, 0 ≤ Q x) (hQle : ∀ x, Q x ≤ 1)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (bR : ∀ x, |R x| ≤ C * Q x) (bS : ∀ x, |S x| ≤ D * Q x) (z : ℝ) :
    |fieldFourthTransform ζ v F M Q R S z| ≤
      (D + 8 * ζ * C + 3 * ζ + 37 * ζ ^ 2) * fieldCurvatureTransform ζ v F M Q z := by
  let μ := (gaussianReal z v).tilted (fun x => ζ * F x)
  have : IsProbabilityMeasure μ := isProbabilityMeasure_tilted
    (integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments z v) hF hG ζ)
  let T := fun A : ℝ → ℝ => ∫ x, A x ∂μ
  let m := T M
  let q := T Q
  let V := T (fun x => (M x - m) ^ 2)
  let rc := T (fun x => R x * M x) - T R * m
  let qv := T (fun x => (Q x) ^ 2) - q ^ 2
  let qc := T (fun x => Q x * (M x - m) ^ 2) - q * V
  let mc := T (fun x => (M x - m) ^ 4) - 3 * V ^ 2
  have bQ : ∀ x, |Q x| ≤ 1 := fun x => by rw [abs_of_nonneg (hQpos x)]; exact hQle x
  have bRb : ∀ x, |R x| ≤ C := fun x => (bR x).trans
    (mul_le_of_le_one_right hC (hQle x))
  have hiQ : Integrable Q μ := Integrable.of_bound hQ.aestronglyMeasurable 1
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using bQ x)
  have hiS : Integrable S μ := (hiQ.const_mul D).mono' hS.aestronglyMeasurable
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using bS x)
  have hSb : |T S| ≤ D * q := by
    calc
      _ ≤ ∫ x, |S x| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ x, D * Q x ∂μ := integral_mono hiS.abs (hiQ.const_mul D) bS
      _ = _ := integral_const_mul _ _
  have hrc : |rc| ≤ 2 * C * q := magnetic_relative_centered_bound μ hM hQ hR bM bQ bR
  have hqv0 := magnetic_nonnegative_spin_variance_bound μ hQ hQpos hQle
  have hqv : |qv| ≤ q := by rw [abs_of_nonneg hqv0.1]; exact hqv0.2
  have hqc : |qc| ≤ 5 * q := magnetic_weighted_variance_bound μ hM hQ bM bQ hQpos
  have hmc : |mc| ≤ 7 * V := magnetic_centered_fourth_cumulant_bound μ hM bM
  have hq : 0 ≤ q := integral_nonneg hQpos
  have hV : 0 ≤ V := integral_nonneg fun x => sq_nonneg _
  have hcurv : fieldCurvatureTransform ζ v F M Q z = q + ζ * V := by
    dsimp only [q, V, m, T]
    rw [magnetic_centered_second μ hM bM]
    rfl
  have he := fieldFourthTransform_centered ζ v (S := S) hF hG hM hQ hR bM bQ bRb z
  change fieldFourthTransform ζ v F M Q R S z =
    T S + 4 * ζ * rc + 3 * ζ * qv + 6 * ζ ^ 2 * qc + ζ ^ 3 * mc at he
  rw [he, hcurv]
  have h4 : |4 * ζ * rc| ≤ 4 * ζ * (2 * C * q) := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 4 * ζ)]
    exact mul_le_mul_of_nonneg_left hrc (by positivity)
  have h3 : |3 * ζ * qv| ≤ 3 * ζ * q := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 3 * ζ)]
    exact mul_le_mul_of_nonneg_left hqv (by positivity)
  have h6 : |6 * ζ ^ 2 * qc| ≤ 6 * ζ ^ 2 * (5 * q) := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 6 * ζ ^ 2)]
    exact mul_le_mul_of_nonneg_left hqc (by positivity)
  have h7 : |ζ ^ 3 * mc| ≤ ζ ^ 3 * (7 * V) := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ ζ ^ 3)]
    exact mul_le_mul_of_nonneg_left hmc (by positivity)
  calc
    _ ≤ |T S| + |4 * ζ * rc| + |3 * ζ * qv| + |6 * ζ ^ 2 * qc| + |ζ ^ 3 * mc| :=
      magnetic_abs_five _ _ _ _ _
    _ ≤ D * q + 4 * ζ * (2 * C * q) + 3 * ζ * q + 6 * ζ ^ 2 * (5 * q) + ζ ^ 3 * (7 * V) := by
      linarith
    _ ≤ (D + 8 * ζ * C + 3 * ζ + 37 * ζ ^ 2) * (q + ζ * V) := by
      let L := D + 8 * ζ * C + 3 * ζ + 30 * ζ ^ 2
      let K := D + 8 * ζ * C + 3 * ζ + 37 * ζ ^ 2
      have hLK : L ≤ K := by dsimp only [L, K]; nlinarith [sq_nonneg ζ]
      have h7K : 7 * ζ ^ 2 ≤ K := by
        dsimp only [K]
        nlinarith [sq_nonneg ζ, mul_nonneg hζ hC]
      have h1 := mul_le_mul_of_nonneg_right hLK hq
      have h2 := mul_le_mul_of_nonneg_right h7K (mul_nonneg hζ hV)
      dsimp only [L, K] at h1 h2
      nlinarith

end InvariantIsing

end

end OAI
