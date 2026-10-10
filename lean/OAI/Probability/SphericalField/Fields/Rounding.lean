import Mathlib
import OAI.Probability.SphericalField.Model

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

namespace SphericalPerceptron

lemma BoundedField.bound_nonneg {H : ℝ} (f : BoundedField H) : 0 ≤ H := (f.nonneg 0).trans (f.le_bound 0)

lemma BoundedField.integrable {H : ℝ} (f : BoundedField H) : Integrable f timeLaw := by
  apply Integrable.mono' (integrable_const H) f.measurable.aestronglyMeasurable
  exact ae_of_all _ (fun u => by simpa only [Real.norm_eq_abs,abs_of_nonneg (f.nonneg u)] using f.le_bound u)

lemma sub_roundLower_lt (N : ℕ) {x : ℝ} (hx : 0 ≤ x) : x-roundLower N x < 1/(N+1:ℕ) := by
  have floor_bound := ((Nat.floor_eq_iff
    (mul_nonneg (by positivity : (0 : ℝ) ≤ (N+1:ℕ)) hx)).mp rfl).2
  unfold roundLower
  rw [sub_lt_iff_lt_add,← add_div,lt_div_iff₀ (by positivity : (0:ℝ)<(N+1:ℕ))]
  simpa only [mul_comm,add_comm] using floor_bound

lemma roundLower_measurable (N : ℕ) : Measurable (roundLower N) := (roundLower_monotone N).measurable

lemma BoundedField.round_error {H : ℝ} (f : BoundedField H) (N : ℕ) (u : Time) :
    |f.round N u-f u| ≤ 1/(N+1:ℕ) := by
  change |roundLower N (f u)-f u| ≤ _
  rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr (roundLower_le N (f.nonneg u)))]
  exact (sub_roundLower_lt N (f.nonneg u)).le

lemma BoundedField.round_abs_integral {H : ℝ} (f : BoundedField H) (N : ℕ) :
    (∫ u, |f.round N u-f u| ∂timeLaw) ≤ 1/(N+1:ℕ) := by
  have h := integral_mono ((f.round N).integrable.sub f.integrable).abs
    (integrable_const (1/(N+1:ℕ):ℝ)) (f.round_error N)
  simpa using h

end SphericalPerceptron
end
end

end OAI
