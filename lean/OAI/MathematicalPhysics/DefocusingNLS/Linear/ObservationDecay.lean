import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI

/-! # Decay of the scalar observation term in the energy inequality -/

open Set Filter Topology MeasureTheory

namespace DefocusingNLS

noncomputable def observationDecayIntegral (c d T : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..T, Real.exp (-c * (T - s)) * Real.exp (-d * s)

theorem observationDecayIntegral_nonneg (c d T : ℝ) (hT : 0 ≤ T) :
    0 ≤ observationDecayIntegral c d T := by
  exact intervalIntegral.integral_nonneg hT (fun _ _ => by positivity)

theorem observationDecayIntegral_le (c d T : ℝ) (hT : 0 ≤ T) :
    observationDecayIntegral c d T ≤ T * Real.exp (-min c d * T) := by
  have hi : IntervalIntegrable (fun s : ℝ =>
      Real.exp (-c * (T - s)) * Real.exp (-d * s)) volume 0 T :=
    (by fun_prop : Continuous (fun s : ℝ =>
      Real.exp (-c * (T - s)) * Real.exp (-d * s))).intervalIntegrable _ _
  have h := intervalIntegral.integral_mono_on hT hi
    (intervalIntegrable_const (c := Real.exp (-min c d * T))) (fun s hs => ?_)
  · simpa only [observationDecayIntegral, intervalIntegral.integral_const, sub_zero,
      smul_eq_mul] using h
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h₁ := mul_le_mul_of_nonneg_right (min_le_left c d) (sub_nonneg.mpr hs.2)
  have h₂ := mul_le_mul_of_nonneg_right (min_le_right c d) hs.1
  nlinarith

theorem tendsto_observationDecayIntegral (c d : ℝ) (hc : 0 < c) (hd : 0 < d) :
    Tendsto (observationDecayIntegral c d) atTop (𝓝 0) := by
  have hdecay : Tendsto (fun T : ℝ => T * Real.exp (-min c d * T)) atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (min c d) (lt_min hc hd)
  exact squeeze_zero' (eventually_ge_atTop (0 : ℝ) |>.mono fun T hT =>
    observationDecayIntegral_nonneg c d T hT)
    (eventually_ge_atTop (0 : ℝ) |>.mono fun T hT =>
      observationDecayIntegral_le c d T hT) hdecay

noncomputable def escapedEnergyBound (c d M C T : ℝ) : ℝ :=
  Real.exp (-c * T) * M ^ 2 + C * observationDecayIntegral c d T

theorem tendsto_escapedEnergyBound (c d M C : ℝ) (hc : 0 < c) (hd : 0 < d) :
    Tendsto (escapedEnergyBound c d M C) atTop (𝓝 0) := by
  change Tendsto (fun T => Real.exp (-c * T) * M ^ 2 +
    C * observationDecayIntegral c d T) atTop (𝓝 0)
  have he : Tendsto (fun T : ℝ => Real.exp (-c * T)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp ((tendsto_const_mul_atBot_of_neg (neg_neg_of_pos hc)).2
      tendsto_id)
  simpa only [zero_mul, mul_zero, add_zero] using
    (he.mul_const (M ^ 2)).add ((tendsto_observationDecayIntegral c d hc hd).const_mul C)

end DefocusingNLS

end OAI
