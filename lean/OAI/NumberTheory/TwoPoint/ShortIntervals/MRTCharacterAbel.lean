import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterSums
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace OAI

/-! Abel-integral bounds for every nonprincipal character, retaining the
explicit modulus q in the bound q * norm(s) / re(s). -/

namespace TwoPointCorrelations

open Finset Filter MeasureTheory
open scoped BigOperators Classical Topology

variable {q : ℕ} [NeZero q]

noncomputable def mrtCharacterSummatory (χ : DirichletCharacter ℂ q) (t : ℝ) : ℂ :=
  ∑ n ∈ Icc 1 ⌊t⌋₊, χ (n : ZMod q)

noncomputable def mrtCharacterAbelKernel (χ : DirichletCharacter ℂ q) (s : ℂ) (t : ℝ) : ℂ :=
  mrtCharacterSummatory χ t * (t : ℂ) ^ (-(s + 1))

noncomputable def mrtCharacterAbelIntegral (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  s * ∫ t in Set.Ioi (1 : ℝ), mrtCharacterAbelKernel χ s t

omit [NeZero q] in
lemma mrtCharacterSummatory_measurable (χ : DirichletCharacter ℂ q) :
    Measurable (mrtCharacterSummatory χ) := by
  exact (measurable_from_nat (f := fun N => ∑ n ∈ Icc 1 N, χ (n : ZMod q))).comp
    Nat.measurable_floor

lemma mrtCharacterSummatory_norm (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (t : ℝ) :
    ‖mrtCharacterSummatory χ t‖ ≤ (q : ℝ) :=
  mrt_character_Icc_norm χ hχ ⌊t⌋₊

omit [NeZero q] in
lemma mrtCharacterAbelKernel_measurable (χ : DirichletCharacter ℂ q) (s : ℂ) :
    AEStronglyMeasurable (mrtCharacterAbelKernel χ s) (volume.restrict (Set.Ioi (1 : ℝ))) := by
  have hpow : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (-(s + 1))) (Set.Ioi (1 : ℝ)) := by
    intro t ht
    exact (Complex.continuousAt_ofReal_cpow_const _ _
      (Or.inr (zero_lt_one.trans ht).ne')).continuousWithinAt
  exact (mrtCharacterSummatory_measurable χ).aestronglyMeasurable.mul
    (hpow.aestronglyMeasurable measurableSet_Ioi)

lemma mrtCharacterAbelKernel_norm_le (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (s : ℂ) {t : ℝ} (ht : 1 < t) :
    ‖mrtCharacterAbelKernel χ s t‖ ≤ (q : ℝ) * t ^ (-(s.re + 1)) := by
  rw [mrtCharacterAbelKernel, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans ht), Complex.neg_re,
    Complex.add_re, Complex.one_re]
  exact mul_le_mul_of_nonneg_right (mrtCharacterSummatory_norm χ hχ t)
    (Real.rpow_nonneg (zero_lt_one.trans ht).le _)

theorem mrtCharacterAbelKernel_integrable (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (mrtCharacterAbelKernel χ s) (Set.Ioi (1 : ℝ)) := by
  have hmajor : IntegrableOn (fun t : ℝ => (q : ℝ) * t ^ (-(s.re + 1))) (Set.Ioi (1 : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -(s.re + 1) < -1) zero_lt_one).const_mul (q : ℝ)
  refine hmajor.mono' (mrtCharacterAbelKernel_measurable χ s) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact mrtCharacterAbelKernel_norm_le χ hχ s ht

lemma mrtCharacterAbelKernel_integral_norm (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) :
    ‖∫ t in Set.Ioi (1 : ℝ), mrtCharacterAbelKernel χ s t‖ ≤ (q : ℝ) / s.re := by
  have hexp : -(s.re + 1) < -1 := by linarith
  calc
    _ ≤ ∫ t in Set.Ioi (1 : ℝ), (q : ℝ) * t ^ (-(s.re + 1)) := by
      apply norm_integral_le_of_norm_le
        ((integrableOn_Ioi_rpow_of_lt hexp zero_lt_one).const_mul (q : ℝ))
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mrtCharacterAbelKernel_norm_le χ hχ s ht
    _ = (q : ℝ) / s.re := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt hexp zero_lt_one, Real.one_rpow]
      field_simp [ne_of_gt hs]
      ring

theorem mrtCharacterAbelIntegral_norm (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) :
    ‖mrtCharacterAbelIntegral χ s‖ ≤ (q : ℝ) * ‖s‖ / s.re := by
  rw [mrtCharacterAbelIntegral, norm_mul]
  calc
    _ ≤ ‖s‖ * ((q : ℝ) / s.re) :=
      mul_le_mul_of_nonneg_left (mrtCharacterAbelKernel_integral_norm χ hχ hs) (norm_nonneg s)
    _ = _ := by ring

theorem mrtCharacterAbelIntegral_eq_LFunction (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 1 < s.re) :
    mrtCharacterAbelIntegral χ s = DirichletCharacter.LFunction χ s :=
  (mrt_character_LFunction_Abel χ hχ hs).symm

end TwoPointCorrelations

end OAI
