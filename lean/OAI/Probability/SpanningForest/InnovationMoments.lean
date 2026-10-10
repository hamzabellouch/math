import Mathlib

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem336.InnovationMoments

theorem abs_square_perturbation_le (q r a : ℝ) (ha : 0 ≤ a) (hr : |r| ≤ a) :
    |(q + r) ^ 2 - q ^ 2| ≤ 2 * a * |q| + a ^ 2 := by
  have hqr : |q * r| ≤ |q| * a := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hr (abs_nonneg q)
  have hqr' := abs_le.mp hqr
  have hr2 : r ^ 2 ≤ a ^ 2 := by
    nlinarith [sq_abs r, mul_nonneg (sub_nonneg.mpr hr) (add_nonneg (abs_nonneg r) ha)]
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg r]

theorem abs_cube_perturbation_le (q r a : ℝ) (ha : 0 ≤ a) (hr : |r| ≤ a) :
    |q + r| ^ 3 ≤ 4 * (|q| ^ 3 + a ^ 3) := by
  have hsum : |q + r| ≤ |q| + a := (abs_add_le q r).trans (add_le_add le_rfl hr)
  have hcube := pow_le_pow_left₀ (abs_nonneg (q + r)) hsum 3
  have hexpand := mul_nonneg (add_nonneg (abs_nonneg q) ha) (sq_nonneg (|q| - a))
  nlinarith

theorem square_perturbation_le (q r a : ℝ) (ha : 0 ≤ a) (hr : |r| ≤ a) :
    (q + r) ^ 2 ≤ 2 * (q ^ 2 + a ^ 2) := by
  have hr2 : r ^ 2 ≤ a ^ 2 := by
    nlinarith [sq_abs r, mul_nonneg (sub_nonneg.mpr hr) (add_nonneg (abs_nonneg r) ha)]
  nlinarith [sq_nonneg (q - r)]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {Q R : Ω → ℝ} {a : ℝ}

theorem integrable_square_add_of_bounded
    (hQ : AEStronglyMeasurable Q μ) (hR : AEStronglyMeasurable R μ)
    (hQ2 : Integrable (fun ω => Q ω ^ 2) μ)
    (ha : 0 ≤ a) (hRbound : ∀ᵐ ω ∂μ, |R ω| ≤ a) :
    Integrable (fun ω => (Q ω + R ω) ^ 2) μ := by
  apply ((hQ2.add (integrable_const (a ^ 2))).const_mul 2).mono'
    ((hQ.add hR).pow 2)
  filter_upwards [hRbound] with ω hω
  change |(Q ω + R ω) ^ 2| ≤ 2 * (Q ω ^ 2 + a ^ 2)
  rw [abs_of_nonneg (sq_nonneg _)]
  exact square_perturbation_le (Q ω) (R ω) a ha hω

theorem integrable_abs_cube_add_of_bounded
    (hQ : AEStronglyMeasurable Q μ) (hR : AEStronglyMeasurable R μ)
    (hQ3 : Integrable (fun ω => |Q ω| ^ 3) μ)
    (ha : 0 ≤ a) (hRbound : ∀ᵐ ω ∂μ, |R ω| ≤ a) :
    Integrable (fun ω => |Q ω + R ω| ^ 3) μ := by
  apply ((hQ3.add (integrable_const (a ^ 3))).const_mul 4).mono'
    (by
      apply ((hQ.add hR).norm.pow 3).congr
      filter_upwards [] with ω
      simp only [Pi.pow_apply, Pi.add_apply, Real.norm_eq_abs])
  filter_upwards [hRbound] with ω hω
  change |(|Q ω + R ω| ^ 3)| ≤ 4 * (|Q ω| ^ 3 + a ^ 3)
  rw [abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
  exact abs_cube_perturbation_le (Q ω) (R ω) a ha hω

theorem integral_square_perturbation_le
    (hQ : Integrable Q μ) (hR : AEStronglyMeasurable R μ)
    (hQ2 : Integrable (fun ω => Q ω ^ 2) μ)
    (ha : 0 ≤ a) (hRbound : ∀ᵐ ω ∂μ, |R ω| ≤ a) :
    |(∫ ω, (Q ω + R ω) ^ 2 ∂μ) - ∫ ω, Q ω ^ 2 ∂μ| ≤
      2 * a * (∫ ω, |Q ω| ∂μ) + a ^ 2 * μ.real Set.univ := by
  have hD2 := integrable_square_add_of_bounded hQ.aestronglyMeasurable hR hQ2 ha hRbound
  have hbound : Integrable (fun ω => 2 * a * |Q ω| + a ^ 2) μ :=
    (hQ.abs.const_mul (2 * a)).add (integrable_const _)
  calc
    _ = |∫ ω, (Q ω + R ω) ^ 2 - Q ω ^ 2 ∂μ| := by
      rw [integral_sub hD2 hQ2]
    _ ≤ ∫ ω, |(Q ω + R ω) ^ 2 - Q ω ^ 2| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ ω, 2 * a * |Q ω| + a ^ 2 ∂μ := by
      apply integral_mono_ae (hD2.sub hQ2).abs hbound
      filter_upwards [hRbound] with ω hω
      exact abs_square_perturbation_le (Q ω) (R ω) a ha hω
    _ = _ := by
      rw [integral_add (hQ.abs.const_mul _) (integrable_const _), integral_const_mul,
        integral_const]
      simp only [smul_eq_mul]
      ring

theorem integral_abs_cube_perturbation_le
    (hQ : AEStronglyMeasurable Q μ) (hR : AEStronglyMeasurable R μ)
    (hQ3 : Integrable (fun ω => |Q ω| ^ 3) μ)
    (ha : 0 ≤ a) (hRbound : ∀ᵐ ω ∂μ, |R ω| ≤ a) :
    (∫ ω, |Q ω + R ω| ^ 3 ∂μ) ≤
      4 * ((∫ ω, |Q ω| ^ 3 ∂μ) + a ^ 3 * μ.real Set.univ) := by
  have hD3 := integrable_abs_cube_add_of_bounded hQ hR hQ3 ha hRbound
  have hbound : Integrable (fun ω => 4 * (|Q ω| ^ 3 + a ^ 3)) μ :=
    (hQ3.add (integrable_const _)).const_mul _
  calc
    _ ≤ ∫ ω, 4 * (|Q ω| ^ 3 + a ^ 3) ∂μ := by
      apply integral_mono_ae hD3 hbound
      filter_upwards [hRbound] with ω hω
      exact abs_cube_perturbation_le (Q ω) (R ω) a ha hω
    _ = _ := by
      rw [integral_const_mul, integral_add hQ3 (integrable_const _), integral_const]
      simp only [smul_eq_mul]
      ring

end Problem336.InnovationMoments

end

end OAI
