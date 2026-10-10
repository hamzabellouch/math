import Mathlib

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal
open scoped BigOperators

namespace Problem336.GaussianBoundedCorrection

theorem abs_sq_add_sub_sq_le (x r a : ℝ) (_ha : 0 ≤ a) (hr : |r| ≤ a) :
    |(x + r) ^ 2 - x ^ 2| ≤ 2 * a * |x| + a ^ 2 := by
  calc
    |(x + r) ^ 2 - x ^ 2| = |2 * x * r + r ^ 2| := by congr 1; ring
    _ ≤ |2 * x * r| + |r ^ 2| := abs_add_le _ _
    _ = 2 * |x| * |r| + |r| ^ 2 := by simp [abs_mul, abs_pow]
    _ ≤ 2 * |x| * a + a ^ 2 := by gcongr
    _ = 2 * a * |x| + a ^ 2 := by ring

theorem abs_add_cube_le (x r a : ℝ) (ha : 0 ≤ a) (hr : |r| ≤ a) :
    |x + r| ^ 3 ≤ 4 * (|x| ^ 3 + a ^ 3) := by
  have habs : |x + r| ≤ |x| + a := (abs_add_le x r).trans (add_le_add le_rfl hr)
  have hcube : |x + r| ^ 3 ≤ (|x| + a) ^ 3 := by gcongr
  have hprod : 0 ≤ (|x| + a) * (|x| - a) ^ 2 :=
    mul_nonneg (add_nonneg (abs_nonneg x) ha) (sq_nonneg _)
  nlinarith

theorem sq_add_le (x r a : ℝ) (_ha : 0 ≤ a) (hr : |r| ≤ a) :
    (x + r) ^ 2 ≤ 2 * (x ^ 2 + a ^ 2) := by
  have habs : |x + r| ≤ |x| + a := (abs_add_le x r).trans (add_le_add le_rfl hr)
  have hsq : |x + r| ^ 2 ≤ (|x| + a) ^ 2 := by gcongr
  have hgap := sq_nonneg (|x| - a)
  simp only [sq_abs] at hsq hgap
  nlinarith [sq_abs x]

section Integral

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

theorem integrable_sq_add_of_bounded {Q R : Ω → ℝ} {a : ℝ}
    (hQ : AEStronglyMeasurable Q μ) (hQ2 : Integrable (fun ω => Q ω ^ 2) μ)
    (hR : AEStronglyMeasurable R μ) (ha : 0 ≤ a)
    (hbound : ∀ᵐ ω ∂μ, |R ω| ≤ a) :
    Integrable (fun ω => (Q ω + R ω) ^ 2) μ := by
  apply ((hQ2.add (integrable_const (a ^ 2))).const_mul 2).mono'
    ((hQ.add hR).pow 2)
  filter_upwards [hbound] with ω hω
  change |(Q ω + R ω) ^ 2| ≤ 2 * (Q ω ^ 2 + a ^ 2)
  rw [abs_of_nonneg (sq_nonneg _)]
  exact sq_add_le (Q ω) (R ω) a ha hω

theorem abs_integral_sq_add_sub_sq_le {Q R : Ω → ℝ} {a : ℝ}
    (hQ : Integrable Q μ) (hQ2 : Integrable (fun ω => Q ω ^ 2) μ)
    (hR : AEStronglyMeasurable R μ) (ha : 0 ≤ a)
    (hbound : ∀ᵐ ω ∂μ, |R ω| ≤ a) :
    |(∫ ω, (Q ω + R ω) ^ 2 ∂μ) - ∫ ω, Q ω ^ 2 ∂μ| ≤
      2 * a * (∫ ω, |Q ω| ∂μ) + μ.real Set.univ * a ^ 2 := by
  have hD2 := integrable_sq_add_of_bounded hQ.aestronglyMeasurable hQ2 hR ha hbound
  have hdom : Integrable (fun ω => 2 * a * |Q ω| + a ^ 2) μ :=
    (hQ.abs.const_mul (2 * a)).add (integrable_const _)
  calc
    |(∫ ω, (Q ω + R ω) ^ 2 ∂μ) - ∫ ω, Q ω ^ 2 ∂μ| =
        |∫ ω, (Q ω + R ω) ^ 2 - Q ω ^ 2 ∂μ| := by rw [integral_sub hD2 hQ2]
    _ ≤ ∫ ω, |(Q ω + R ω) ^ 2 - Q ω ^ 2| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ ω, 2 * a * |Q ω| + a ^ 2 ∂μ := by
      apply integral_mono_ae (hD2.sub hQ2).abs hdom
      filter_upwards [hbound] with ω hω
      exact abs_sq_add_sub_sq_le (Q ω) (R ω) a ha hω
    _ = 2 * a * (∫ ω, |Q ω| ∂μ) + μ.real Set.univ * a ^ 2 := by
      rw [integral_add (hQ.abs.const_mul _) (integrable_const _),
        integral_const_mul, integral_const]
      rfl

theorem integrable_abs_cube_add_of_bounded {Q R : Ω → ℝ} {a : ℝ}
    (hQ : AEStronglyMeasurable Q μ) (hQ3 : Integrable (fun ω => |Q ω| ^ 3) μ)
    (hR : AEStronglyMeasurable R μ) (ha : 0 ≤ a)
    (hbound : ∀ᵐ ω ∂μ, |R ω| ≤ a) :
    Integrable (fun ω => |Q ω + R ω| ^ 3) μ := by
  have hm : AEStronglyMeasurable (fun ω => |Q ω + R ω| ^ 3) μ := by
    exact (continuous_abs.pow 3).comp_aestronglyMeasurable (hQ.add hR)
  apply ((hQ3.add (integrable_const (a ^ 3))).const_mul 4).mono' hm
  filter_upwards [hbound] with ω hω
  change |(|Q ω + R ω| ^ 3)| ≤ 4 * (|Q ω| ^ 3 + a ^ 3)
  rw [abs_of_nonneg (pow_nonneg (abs_nonneg _) 3)]
  exact abs_add_cube_le (Q ω) (R ω) a ha hω

theorem integral_abs_cube_add_le {Q R : Ω → ℝ} {a : ℝ}
    (hQ : AEStronglyMeasurable Q μ) (hQ3 : Integrable (fun ω => |Q ω| ^ 3) μ)
    (hR : AEStronglyMeasurable R μ) (ha : 0 ≤ a)
    (hbound : ∀ᵐ ω ∂μ, |R ω| ≤ a) :
    (∫ ω, |Q ω + R ω| ^ 3 ∂μ) ≤
      4 * ((∫ ω, |Q ω| ^ 3 ∂μ) + μ.real Set.univ * a ^ 3) := by
  calc
    (∫ ω, |Q ω + R ω| ^ 3 ∂μ) ≤ ∫ ω, 4 * (|Q ω| ^ 3 + a ^ 3) ∂μ := by
      apply integral_mono_ae (integrable_abs_cube_add_of_bounded hQ hQ3 hR ha hbound)
        ((hQ3.add (integrable_const _)).const_mul _)
      filter_upwards [hbound] with ω hω
      exact abs_add_cube_le (Q ω) (R ω) a ha hω
    _ = 4 * ((∫ ω, |Q ω| ^ 3 ∂μ) + μ.real Set.univ * a ^ 3) := by
      rw [integral_const_mul, integral_add hQ3 (integrable_const _), integral_const]
      rfl

end Integral

def standardGaussianAbsMoment (k : ℕ) : ℝ :=
  ∫ x : ℝ, |x| ^ k ∂gaussianReal 0 1

theorem standardGaussianAbsMoment_nonneg (k : ℕ) :
    0 ≤ standardGaussianAbsMoment k :=
  integral_nonneg (fun x => pow_nonneg (abs_nonneg x) k)

theorem gaussian_abs_moment (v : ℝ≥0) (k : ℕ) :
    (∫ x : ℝ, |x| ^ k ∂gaussianReal 0 v) =
      Real.sqrt v ^ k * standardGaussianAbsMoment k := by
  have hs : (⟨Real.sqrt v ^ 2, sq_nonneg _⟩ : ℝ≥0) = v :=
    NNReal.eq (Real.sq_sqrt v.property)
  have hscale : (gaussianReal 0 1).map (fun x : ℝ => Real.sqrt v * x) =
      gaussianReal 0 v := by
    rw [gaussianReal_map_const_mul, mul_zero, mul_one]
    congr 1
  rw [← hscale, integral_map (by fun_prop) (by fun_prop)]
  simp_rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow]
  exact integral_const_mul _ _

theorem hasLaw_gaussian_abs_moment {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Q : Ω → ℝ} {v : ℝ≥0}
    (hQ : HasLaw Q (gaussianReal 0 v) P) (k : ℕ) :
    (∫ ω, |Q ω| ^ k ∂P) = Real.sqrt v ^ k * standardGaussianAbsMoment k := by
  calc
    (∫ ω, |Q ω| ^ k ∂P) = ∫ x : ℝ, |x| ^ k ∂gaussianReal 0 v := by
      exact hQ.integral_comp (f := fun x : ℝ => |x| ^ k) (by fun_prop)
    _ = _ := gaussian_abs_moment v k

theorem hasLaw_gaussian_integral_sq {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Q : Ω → ℝ} {v : ℝ≥0}
    (hQ : HasLaw Q (gaussianReal 0 v) P) :
    (∫ ω, Q ω ^ 2 ∂P) = v := by
  have hm : (∫ ω, Q ω ∂P) = 0 := by
    rw [hQ.integral_eq, integral_id_gaussianReal]
  have hv := hQ.variance_eq
  rw [variance_eq_integral hQ.aemeasurable, hm] at hv
  simpa only [sub_zero, variance_id_gaussianReal] using hv

theorem gaussian_bounded_correction_second_moment
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Q R : Ω → ℝ} {v : ℝ≥0} {a : ℝ}
    (hQ : HasLaw Q (gaussianReal 0 v) P)
    (hR : AEStronglyMeasurable R P) (ha : 0 ≤ a)
    (hbound : ∀ᵐ ω ∂P, |R ω| ≤ a) :
    |(∫ ω, (Q ω + R ω) ^ 2 ∂P) - v| ≤
      2 * a * Real.sqrt v * standardGaussianAbsMoment 1 + a ^ 2 := by
  let : IsProbabilityMeasure P := hQ.isProbabilityMeasure
  have hint := hQ.hasGaussianLaw.integrable
  have hQ2 : Integrable (fun ω => Q ω ^ 2) P :=
    (memLp_two_iff_integrable_sq hint.aestronglyMeasurable).mp hQ.hasGaussianLaw.memLp_two
  have h := abs_integral_sq_add_sub_sq_le hint hQ2 hR ha hbound
  rw [hasLaw_gaussian_integral_sq hQ] at h
  have hfirst : (∫ ω, |Q ω| ∂P) = Real.sqrt v * standardGaussianAbsMoment 1 := by
    simpa only [pow_one] using hasLaw_gaussian_abs_moment hQ 1
  simpa only [hfirst, probReal_univ, one_mul, mul_assoc] using h

theorem gaussian_bounded_correction_third_moment
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Q R : Ω → ℝ} {v : ℝ≥0} {a : ℝ}
    (hQ : HasLaw Q (gaussianReal 0 v) P)
    (hR : AEStronglyMeasurable R P) (ha : 0 ≤ a)
    (hbound : ∀ᵐ ω ∂P, |R ω| ≤ a) :
    (∫ ω, |Q ω + R ω| ^ 3 ∂P) ≤
      4 * (Real.sqrt v ^ 3 * standardGaussianAbsMoment 3 + a ^ 3) := by
  let : IsProbabilityMeasure P := hQ.isProbabilityMeasure
  have hQ3 : Integrable (fun ω => |Q ω| ^ 3) P := by
    simpa only [Real.norm_eq_abs] using
      (hQ.hasGaussianLaw.memLp (p := 3) (by norm_num)).integrable_norm_pow (by norm_num : 3 ≠ 0)
  have h := integral_abs_cube_add_le hQ.aemeasurable.aestronglyMeasurable hQ3 hR ha hbound
  simpa only [hasLaw_gaussian_abs_moment hQ 3, probReal_univ, one_mul] using h

end Problem336.GaussianBoundedCorrection

end

end OAI
