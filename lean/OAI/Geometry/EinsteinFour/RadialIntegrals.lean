import OAI.Geometry.EinsteinFour.SineEstimates

namespace OAI

/-! The two analytic integral margins in the volume comparison. All numerical
bounds here follow from exact polynomial integrals and the proved sine bound;
no numerical integration or decimal error premise is used. -/

namespace PositiveEinsteinFour.VolumeConstants

open MeasureTheory

noncomputable section

def upperKernel (u : ℝ) : ℝ :=
  (9 * Real.pi / 48) * initialFactor u * (1 - u ^ 2 / 2) * Real.sin (Real.pi * u) ^ 3

def upperKernelEnd (u : ℝ) : ℝ :=
  (9 * Real.pi / 48) * (15 / 16) * (1 - u ^ 2 / 2) * Real.sin (Real.pi * u) ^ 3

def lowerKernel (u : ℝ) : ℝ :=
  (Real.pi ^ 3 / 27) * u ^ 2 * (u ^ 4 / 2 + u ^ 6 / 3) * Real.sin (Real.pi * u)

private theorem upper_comparison {u z A : ℝ}
    (hu : 0 ≤ u) (hu1 : u ≤ 1) (hA : 0 ≤ A)
    (hz0 : 0 ≤ sineLower z) (hz : sineLower z ≤ Real.sin (Real.pi * u)) :
    (9 * (157 / 50) / 48) * A * (1 - u ^ 2 / 2) * sineLower z ^ 3 ≤
      (9 * Real.pi / 48) * A * (1 - u ^ 2 / 2) * Real.sin (Real.pi * u) ^ 3 := by
  have hpi : (157 / 50 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d2]
  have hw : 0 ≤ 1 - u ^ 2 / 2 := by nlinarith
  gcongr

private theorem lower_comparison {u z : ℝ} (_hu : 0 ≤ u)
    (hz0 : 0 ≤ sineLower z) (hz : sineLower z ≤ Real.sin (Real.pi * u)) :
    ((157 / 50) ^ 3 / 27) * u ^ 2 * (u ^ 4 / 2 + u ^ 6 / 3) * sineLower z ≤
      lowerKernel u := by
  have hpi : (157 / 50 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d2]
  unfold lowerKernel
  gcongr

private theorem sine_reflected_bound {u : ℝ} (hu : 1 / 2 ≤ u) (hu1 : u ≤ 1) :
    0 ≤ sineLower (1 - u) ∧ sineLower (1 - u) ≤ Real.sin (Real.pi * u) := by
  have h := reflected_sineLower (by linarith : 0 ≤ u) hu1
  rwa [min_eq_right (by linarith)] at h

private theorem upper_integral_first :
    (∫ u in (0 : ℝ)..(1 / 2), upperIntegrand u) ≤
      ∫ u in (0 : ℝ)..(1 / 2), upperKernel u := by
  apply intervalIntegral.integral_mono_on (by norm_num)
    (by apply Continuous.intervalIntegrable; unfold upperIntegrand initialFactor sineLower; fun_prop)
    (by apply Continuous.intervalIntegrable; unfold upperKernel initialFactor; fun_prop)
  intro u hu
  have hsin := sineLower_le_sin hu.1
  have hnonneg := sineLower_nonneg hu.1 hu.2
  exact upper_comparison hu.1 (by linarith [hu.2])
    (by unfold initialFactor; positivity) hnonneg hsin

private theorem upper_integral_middle :
    (∫ u in (1 / 2 : ℝ)..(5 / 8), upperIntegrandMiddle u) ≤
      ∫ u in (1 / 2 : ℝ)..(5 / 8), upperKernel u := by
  apply intervalIntegral.integral_mono_on (by norm_num)
    (by apply Continuous.intervalIntegrable; unfold upperIntegrandMiddle initialFactor sineLower; fun_prop)
    (by apply Continuous.intervalIntegrable; unfold upperKernel initialFactor; fun_prop)
  intro u hu
  have hsin := sine_reflected_bound hu.1 (by linarith [hu.2])
  exact upper_comparison (by linarith [hu.1]) (by linarith [hu.2])
    (by unfold initialFactor; positivity) hsin.1 hsin.2

private theorem upper_integral_end :
    (∫ u in (5 / 8 : ℝ)..1, upperIntegrandEnd u) ≤
      ∫ u in (5 / 8 : ℝ)..1, upperKernelEnd u := by
  apply intervalIntegral.integral_mono_on (by norm_num)
    (by apply Continuous.intervalIntegrable; unfold upperIntegrandEnd sineLower; fun_prop)
    (by apply Continuous.intervalIntegrable; unfold upperKernelEnd; fun_prop)
  intro u hu
  have hsin := sine_reflected_bound (by linarith [hu.1]) hu.2
  exact upper_comparison (by linarith [hu.1]) hu.2 (by norm_num) hsin.1 hsin.2

/-- The actual upper-volume deficit coefficient exceeds the constant required
by the classification argument. The two pieces are precisely the integral
of the manuscript's piecewise weight. -/
theorem analytic_upper_margin : (3 / 40 : ℝ) <
    (∫ u in (0 : ℝ)..(5 / 8), upperKernel u) +
      ∫ u in (5 / 8 : ℝ)..1, upperKernelEnd u := by
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (f := upperKernel) (μ := volume)
    (a := (0 : ℝ)) (b := (1 / 2 : ℝ)) (c := (5 / 8 : ℝ))
    (by apply Continuous.intervalIntegrable; unfold upperKernel initialFactor; fun_prop)
    (by apply Continuous.intervalIntegrable; unfold upperKernel initialFactor; fun_prop)
  linarith [upper_margin, upper_integral_first, upper_integral_middle, upper_integral_end]

private theorem lower_integral_first :
    (∫ u in (0 : ℝ)..(1 / 2), lowerIntegrand u) ≤
      ∫ u in (0 : ℝ)..(1 / 2), lowerKernel u := by
  apply intervalIntegral.integral_mono_on (by norm_num)
    (by apply Continuous.intervalIntegrable; unfold lowerIntegrand sineLower; fun_prop)
    (by apply Continuous.intervalIntegrable; unfold lowerKernel; fun_prop)
  intro u hu
  exact lower_comparison hu.1 (sineLower_nonneg hu.1 hu.2) (sineLower_le_sin hu.1)

private theorem lower_integral_end :
    (∫ u in (1 / 2 : ℝ)..1, lowerIntegrandEnd u) ≤
      ∫ u in (1 / 2 : ℝ)..1, lowerKernel u := by
  apply intervalIntegral.integral_mono_on (by norm_num)
    (by apply Continuous.intervalIntegrable; unfold lowerIntegrandEnd sineLower; fun_prop)
    (by apply Continuous.intervalIntegrable; unfold lowerKernel; fun_prop)
  intro u hu
  have hsin := sine_reflected_bound hu.1 hu.2
  exact lower_comparison (by linarith [hu.1]) hsin.1 hsin.2

/-- The lower radial integral exceeds `4/3`, with its strict margin supplied
by the exact rational certificates. -/
theorem analytic_lower_margin : (4 / 3 : ℝ) <
    2 * (Real.pi ^ 2 - 4) / 9 + ∫ u in (0 : ℝ)..1, lowerKernel u := by
  have hpi : (157 / 50 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d2]
  have hbase : 2 * ((157 / 50 : ℝ) ^ 2 - 4) / 9 ≤ 2 * (Real.pi ^ 2 - 4) / 9 := by
    nlinarith [Real.pi_pos]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (f := lowerKernel) (μ := volume) (a := (0 : ℝ)) (b := (1 / 2 : ℝ)) (c := (1 : ℝ))
    (by apply Continuous.intervalIntegrable; unfold lowerKernel; fun_prop) (by apply Continuous.intervalIntegrable; unfold lowerKernel; fun_prop)
  linarith [lower_margin, lower_integral_first, lower_integral_end]

end

end PositiveEinsteinFour.VolumeConstants

end OAI
