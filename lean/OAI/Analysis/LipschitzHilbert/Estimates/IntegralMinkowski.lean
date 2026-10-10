import OAI.Analysis.LipschitzHilbert.Estimates.MixedNorms
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

namespace OAI

/-! Finite Minkowski inequality in the integral form needed by the
diagonal Hilbert extension. -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert.PhaseCombinatorics

theorem lpNorm_nonnegative_eq (ν : Measure ℝ) (f : ℝ → ℝ)
    (hf : Continuous f) (hpos : ∀ t, 0 ≤ f t) {p : ℝ} (hp : 0 < p) :
    lpNorm f (ENNReal.ofReal p) ν = (∫ t, f t ^ p ∂ν) ^ (1 / p) := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by positivity) ENNReal.ofReal_ne_top
    hf.aestronglyMeasurable, ENNReal.toReal_ofReal hp.le]
  simp only [Real.norm_eq_abs, abs_of_nonneg (hpos _), one_div]

theorem integral_finite_minkowski {κ : Type*} [Fintype κ]
    (ν : Measure ℝ) [IsFiniteMeasure ν] (f : κ → ℝ → ℝ) (B : κ → ℝ)
    (hf : ∀ j, Continuous (f j)) (hpos : ∀ j t, 0 ≤ f j t)
    (hbound : ∀ j t, f j t ≤ B j) {p : ℝ} (hp : 1 ≤ p) :
    (∫ t, (∑ j, f j t) ^ p ∂ν) ^ (1 / p) ≤
      ∑ j, (∫ t, f j t ^ p ∂ν) ^ (1 / p) := by
  have hp0 : 0 < p := by linarith
  have hmem (j : κ) : MemLp (f j) (ENNReal.ofReal p) ν := by
    apply MemLp.of_bound (hf j).aestronglyMeasurable (B j)
    exact Filter.Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hpos j t)]
      exact hbound j t
  have hp' : 1 ≤ ENNReal.ofReal p := by
    exact ENNReal.one_le_ofReal.mpr hp
  have h := lpNorm_sum_le (s := Finset.univ) (fun j _ => hmem j) hp'
  have hcont : Continuous (fun t => ∑ j, f j t) :=
    continuous_finsetSum _ (fun j _ => hf j)
  have hnonneg (t : ℝ) : 0 ≤ ∑ j, f j t :=
    Finset.sum_nonneg (fun j _ => hpos j t)
  have heq : (∑ j, f j) = (fun t => ∑ j, f j t) := by
    funext t
    exact Finset.sum_apply _ _ _
  rw [heq, lpNorm_nonnegative_eq ν _ hcont hnonneg hp0] at h
  simpa only [lpNorm_nonnegative_eq ν _ (hf _) (hpos _) hp0] using h

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
