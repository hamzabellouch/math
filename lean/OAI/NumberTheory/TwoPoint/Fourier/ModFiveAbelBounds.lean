import OAI.NumberTheory.TwoPoint.Fourier.ModFiveCharacterSums
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace OAI

/-! Uniform Abel-integral estimates for the nonprincipal modulus-five
characters. The integral converges throughout `re s > 0`; its norm is at most
`4 * ‖s‖ / re s`, using the exact period bound rather than a new input.
-/

namespace TwoPointCorrelations

open Finset Filter MeasureTheory
open scoped BigOperators Classical Topology

noncomputable def modFiveSummatory (χ : DirichletCharacter ℂ 5) (t : ℝ) : ℂ :=
  ∑ n ∈ Icc 1 ⌊t⌋₊, χ (n : ZMod 5)

noncomputable def modFiveAbelKernel (χ : DirichletCharacter ℂ 5) (s : ℂ) (t : ℝ) : ℂ :=
  modFiveSummatory χ t * (t : ℂ) ^ (-(s + 1))

noncomputable def modFiveAbelIntegral (χ : DirichletCharacter ℂ 5) (s : ℂ) : ℂ :=
  s * ∫ t in Set.Ioi (1 : ℝ), modFiveAbelKernel χ s t

lemma modFiveSummatory_measurable (χ : DirichletCharacter ℂ 5) :
    Measurable (modFiveSummatory χ) := by
  exact (measurable_from_nat (f := fun N => ∑ n ∈ Icc 1 N, χ (n : ZMod 5))).comp
    Nat.measurable_floor

lemma modFiveSummatory_norm (χ : DirichletCharacter ℂ 5) (hχ : χ ≠ 1) (t : ℝ) :
    ‖modFiveSummatory χ t‖ ≤ 4 :=
  modFive_character_Icc_norm χ hχ ⌊t⌋₊

lemma modFiveAbelKernel_measurable (χ : DirichletCharacter ℂ 5) (s : ℂ) :
    AEStronglyMeasurable (modFiveAbelKernel χ s) (volume.restrict (Set.Ioi (1 : ℝ))) := by
  have hpow : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (-(s + 1))) (Set.Ioi (1 : ℝ)) := by
    intro t ht
    exact (Complex.continuousAt_ofReal_cpow_const _ _
      (Or.inr (zero_lt_one.trans ht).ne')).continuousWithinAt
  exact (modFiveSummatory_measurable χ).aestronglyMeasurable.mul
    (hpow.aestronglyMeasurable measurableSet_Ioi)

lemma modFiveAbelKernel_norm_le (χ : DirichletCharacter ℂ 5) (hχ : χ ≠ 1)
    (s : ℂ) {t : ℝ} (ht : 1 < t) :
    ‖modFiveAbelKernel χ s t‖ ≤ 4 * t ^ (-(s.re + 1)) := by
  rw [modFiveAbelKernel, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans ht), Complex.neg_re,
    Complex.add_re, Complex.one_re]
  exact mul_le_mul_of_nonneg_right (modFiveSummatory_norm χ hχ t)
    (Real.rpow_nonneg (zero_lt_one.trans ht).le _)

theorem modFiveAbelKernel_integrable (χ : DirichletCharacter ℂ 5) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (modFiveAbelKernel χ s) (Set.Ioi (1 : ℝ)) := by
  have hmajor : IntegrableOn (fun t : ℝ => 4 * t ^ (-(s.re + 1))) (Set.Ioi (1 : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -(s.re + 1) < -1) zero_lt_one).const_mul 4
  refine hmajor.mono' (modFiveAbelKernel_measurable χ s) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact modFiveAbelKernel_norm_le χ hχ s ht

lemma modFiveAbelKernel_integral_norm (χ : DirichletCharacter ℂ 5) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) :
    ‖∫ t in Set.Ioi (1 : ℝ), modFiveAbelKernel χ s t‖ ≤ 4 / s.re := by
  have hexp : -(s.re + 1) < -1 := by linarith
  calc
    _ ≤ ∫ t in Set.Ioi (1 : ℝ), 4 * t ^ (-(s.re + 1)) := by
      apply norm_integral_le_of_norm_le
        ((integrableOn_Ioi_rpow_of_lt hexp zero_lt_one).const_mul 4)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact modFiveAbelKernel_norm_le χ hχ s ht
    _ = 4 / s.re := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt hexp zero_lt_one, Real.one_rpow]
      field_simp [ne_of_gt hs]
      ring

theorem modFiveAbelIntegral_norm (χ : DirichletCharacter ℂ 5) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) :
    ‖modFiveAbelIntegral χ s‖ ≤ 4 * ‖s‖ / s.re := by
  rw [modFiveAbelIntegral, norm_mul]
  calc
    _ ≤ ‖s‖ * (4 / s.re) :=
      mul_le_mul_of_nonneg_left (modFiveAbelKernel_integral_norm χ hχ hs) (norm_nonneg s)
    _ = _ := by ring

theorem modFiveAbelIntegral_eq_LFunction (χ : DirichletCharacter ℂ 5) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 1 < s.re) :
    modFiveAbelIntegral χ s = DirichletCharacter.LFunction χ s :=
  (modFive_LFunction_Abel χ hχ hs).symm

end TwoPointCorrelations

end OAI
