import OAI.NumberTheory.TwoPoint.Bounds.FiniteProbability
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace OAI

/-! A direct finite-law small-ball inequality using a nonnegative triangular
Fourier kernel. This replaces any need for an external concentration theorem. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

noncomputable def triangleKernel (x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, (1 - t) * Real.cos (t * x)

lemma triangleKernel_zero : triangleKernel 0 = 1 / 2 := by
  unfold triangleKernel
  simp only [mul_zero, Real.cos_zero, mul_one]
  rw [intervalIntegral.integral_sub (f := fun _ : ℝ => 1) (g := fun t : ℝ => t)
    intervalIntegrable_const (continuous_id.intervalIntegrable _ _)]
  norm_num [integral_id]

lemma triangleKernel_eq {x : ℝ} (hx : x ≠ 0) : triangleKernel x = (1 - Real.cos x) / x ^ 2 := by
  let F : ℝ → ℝ := fun t => (1 - t) * Real.sin (t * x) / x - Real.cos (t * x) / x ^ 2
  have hF (t : ℝ) : HasDerivAt F ((1 - t) * Real.cos (t * x)) t := by
    have hs := (Real.hasDerivAt_sin (t * x)).comp t ((hasDerivAt_id t).mul_const x)
    have hc := (Real.hasDerivAt_cos (t * x)).comp t ((hasDerivAt_id t).mul_const x)
    have hh := ((((hasDerivAt_id t).const_sub 1).mul hs).div_const x).sub (hc.div_const (x ^ 2))
    convert hh using 1
    · rfl
    · simp only [Function.comp_apply, id_eq]
      field_simp
      ring
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t (_ : t ∈ Set.uIcc (0 : ℝ) 1) => hF t)
    ((by fun_prop : Continuous (fun t : ℝ => (1 - t) * Real.cos (t * x))).intervalIntegrable _ _)
  change triangleKernel x = _ at hh
  simp [F] at hh
  rw [hh]
  ring

lemma triangleKernel_nonneg (x : ℝ) : 0 ≤ triangleKernel x := by
  by_cases hx : x = 0
  · rw [hx, triangleKernel_zero]; norm_num
  · rw [triangleKernel_eq hx]
    exact div_nonneg (sub_nonneg.mpr (Real.cos_le_one x)) (sq_nonneg x)

lemma triangleKernel_unit_lower (x : ℝ) (hx : |x| ≤ 1) : 1 / 4 ≤ triangleKernel x := by
  have hmono : (∫ t in (0 : ℝ)..1, (1 - t) / 2) ≤ triangleKernel x := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      ((by fun_prop : Continuous (fun t : ℝ => (1 - t) / 2)).intervalIntegrable _ _)
      ((by fun_prop : Continuous (fun t : ℝ => (1 - t) * Real.cos (t * x))).intervalIntegrable _ _)
    intro t ht
    have htx : |t * x| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg ht.1]
      simpa using mul_le_mul ht.2 hx (abs_nonneg x) (by norm_num : (0 : ℝ) ≤ 1)
    have htx' := abs_le.mp htx
    have hsq : (t * x) ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - t * x) (by linarith : 0 ≤ 1 + t * x)]
    have hcos : 1 / 2 ≤ Real.cos (t * x) := by
      have hh := Real.one_sub_sq_div_two_le_cos (x := t * x)
      linarith
    have hh := mul_le_mul_of_nonneg_left hcos (sub_nonneg.mpr ht.2)
    nlinarith
  have hi : (∫ t in (0 : ℝ)..1, (1 - t) / 2) = 1 / 4 := by
    rw [intervalIntegral.integral_div, intervalIntegral.integral_sub
      (f := fun _ : ℝ => 1) (g := fun t : ℝ => t)
      intervalIntegrable_const (continuous_id.intervalIntegrable _ _)]
    norm_num [integral_id]
  rwa [hi] at hmono

lemma FiniteLaw.average_triangleKernel {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (Z : Ω → ℝ) :
    μ.average (fun x => triangleKernel (Z x)) =
      ∫ t in (0 : ℝ)..1, (1 - t) * μ.average (fun x => Real.cos (t * Z x)) := by
  unfold FiniteLaw.average triangleKernel
  calc
    _ = ∑ x, ∫ t in (0 : ℝ)..1, μ.weight x * ((1 - t) * Real.cos (t * Z x)) := by
      apply sum_congr rfl
      intro x _
      rw [intervalIntegral.integral_const_mul]
    _ = ∫ t in (0 : ℝ)..1, ∑ x, μ.weight x * ((1 - t) * Real.cos (t * Z x)) := by
      exact (intervalIntegral.integral_finsetSum (fun x _ =>
        (by fun_prop : Continuous (fun t : ℝ => μ.weight x * ((1 - t) * Real.cos (t * Z x)))).intervalIntegrable _ _)).symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro t _
      change (∑ x, μ.weight x * ((1 - t) * Real.cos (t * Z x))) =
        (1 - t) * ∑ x, μ.weight x * Real.cos (t * Z x)
      rw [mul_sum]
      apply sum_congr rfl
      intro x _
      ring

/-- The exact finite-law small-ball reduction. The characteristic function
can now be bounded inside a compact ordinary integral. -/
theorem FiniteLaw.unit_small_ball_le {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (Z : Ω → ℝ) :
    μ.probability (fun x => |Z x| ≤ 1) ≤
      4 * (∫ t in (0 : ℝ)..1, (1 - t) * μ.average (fun x => Real.cos (t * Z x))) := by
  calc
    _ ≤ μ.average (fun x => triangleKernel (Z x) * 4) := by
      apply μ.average_mono
      intro x
      by_cases hx : |Z x| ≤ 1
      · simp only [hx, ↓reduceIte]
        linarith [triangleKernel_unit_lower (Z x) hx]
      · simp only [hx, ↓reduceIte]
        exact mul_nonneg (triangleKernel_nonneg _) (by norm_num)
    _ = _ := by rw [μ.average_mul_const, μ.average_triangleKernel]; ring

end TwoPointCorrelations

end OAI
