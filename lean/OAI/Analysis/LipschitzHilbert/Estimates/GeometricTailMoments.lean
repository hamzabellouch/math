import OAI.Analysis.LipschitzHilbert.Estimates.GeometricTailExponential
import Mathlib.Probability.Moments.IntegrableExpMul

namespace OAI

/-! Real-power moment bounds from the geometric distribution estimate. -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LipschitzHilbert

theorem geometric_tail_rpow_moment {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (f : X → ℝ) (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) {H : ℝ} (hH : 0 < H)
    (htail : ∀ n : ℕ, μ.real {x | (n : ℝ) * H < f x} ≤
      (1 / 2 : ℝ) ^ n * μ.real univ) {p : ℝ} (hp : 0 ≤ p) :
    (∫⁻ x, ENNReal.ofReal (f x ^ p) ∂μ) ≤
      7 * ENNReal.ofReal ((p * H / Real.log (3 / 2)) ^ p) * μ univ := by
  let t : ℝ := Real.log (3 / 2) / H
  have hlog : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
  have ht : 0 < t := div_pos hlog hH
  have hcoef : p / t = p * H / Real.log (3 / 2) := by
    dsimp [t]
    field_simp
  let K : ℝ := (p * H / Real.log (3 / 2)) ^ p
  have hK : 0 ≤ K := Real.rpow_nonneg (by positivity) _
  have hpoint (x : X) : f x ^ p ≤ K * ((3 / 2 : ℝ) ^ (f x / H)) := by
    have h := ProbabilityTheory.rpow_abs_le_mul_exp_abs (f x) hp ht.ne'
    rw [abs_of_pos ht, abs_of_nonneg (hf0 x), hcoef] at h
    have hexp : Real.exp (t * f x) = (3 / 2 : ℝ) ^ (f x / H) := by
      rw [Real.rpow_def_of_pos (by norm_num)]
      congr 1
      dsimp [t]
      ring
    simpa only [hexp, K] using h
  have hpoint' (x : X) : ENNReal.ofReal (f x ^ p) ≤
      ENNReal.ofReal K * ENNReal.ofReal ((3 / 2 : ℝ) ^ (f x / H)) := by
    simpa only [ENNReal.ofReal_mul hK] using ENNReal.ofReal_le_ofReal (hpoint x)
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal K * ENNReal.ofReal ((3 / 2 : ℝ) ^ (f x / H)) ∂μ :=
      lintegral_mono hpoint'
    _ = ENNReal.ofReal K * ∫⁻ x, ENNReal.ofReal ((3 / 2 : ℝ) ^ (f x / H)) ∂μ :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal K * (7 * μ univ) :=
      mul_le_mul_right (geometric_tail_exponential μ f hf hf0 hH htail) _
    _ = _ := by dsimp [K]; ring

end LipschitzHilbert

end

end OAI
