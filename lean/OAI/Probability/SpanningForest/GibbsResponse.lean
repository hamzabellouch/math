import OAI.Probability.SpanningForest.GibbsField
import OAI.Probability.SpanningForest.ResponseLipschitz

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem336.GibbsField

variable {α ι : Type*} [Fintype α] [Fintype ι]

theorem coordinate_mean_eq_finiteResponse (x : α → ι → ℝ) (h : ι → ℝ) (e : ι) :
    mean x (fun i => x i e) h = FiniteResponse.mean (mass x h) x e :=
  mean_eq_sum_mass x (fun i => x i e) h

theorem coordinate_covariance_eq_finiteResponse
    (x : α → ι → ℝ) (h : ι → ℝ) (e f : ι) :
    covariance x (fun i => x i e) (fun i => x i f) h =
      FiniteResponse.covariance (mass x h) x e f := by
  simp only [covariance, FiniteResponse.covariance, mean_eq_sum_mass,
    FiniteResponse.mean, mul_assoc]

theorem covariance_abs_row_le_half [Nonempty α]
    (x : α → ι → ℝ)
    (hx : ∀ i e, x i e = 0 ∨ x i e = 1)
    (r : ℝ) (hfixed : ∀ i, ∑ f, x i f = r)
    (h : ι → ℝ)
    (hneg : ∀ e f, e ≠ f → covariance x (fun i => x i e) (fun i => x i f) h ≤ 0)
    (e : ι) :
    (∑ f, |covariance x (fun i => x i e) (fun i => x i f) h|) ≤ (1 : ℝ) / 2 := by
  simp_rw [coordinate_covariance_eq_finiteResponse] at hneg ⊢
  exact FiniteResponse.covariance_abs_row_le_half (mass x h) x
    (mass_nonneg x h) (sum_mass x h) hx r hfixed hneg e

theorem response_bound [Nonempty α]
    (x : α → ι → ℝ)
    (hx : ∀ i e, x i e = 0 ∨ x i e = 1)
    (r : ℝ) (hfixed : ∀ i, ∑ f, x i f = r)
    (hneg : ∀ h e f, e ≠ f →
      covariance x (fun i => x i e) (fun i => x i f) h ≤ 0)
    (a b : ι → ℝ) (e : ι) :
    |mean x (fun i => x i e) b - mean x (fun i => x i e) a| ≤
      (1 / 2 : ℝ) * ‖b - a‖ := by
  apply FiniteResponse.abs_sub_le_of_line_derivative_row_bound
    (f := mean x (fun i => x i e))
    (c := fun h f => covariance x (fun i => x i e) (fun i => x i f) h)
  · intro h k t
    apply (hasDerivAt_mean_direction_sum x (fun i => x i e) h (k - h) t).congr_deriv
    apply Finset.sum_congr rfl
    intro f _
    exact mul_comm _ _
  · intro h
    exact covariance_abs_row_le_half x hx r hfixed h (hneg h) e

theorem response_bound_of_coordinate_bound [Nonempty α]
    (x : α → ι → ℝ)
    (hx : ∀ i e, x i e = 0 ∨ x i e = 1)
    (r : ℝ) (hfixed : ∀ i, ∑ f, x i f = r)
    (hneg : ∀ h e f, e ≠ f →
      covariance x (fun i => x i e) (fun i => x i f) h ≤ 0)
    (a b : ι → ℝ) (e : ι) (D : ℝ) (hD : 0 ≤ D)
    (hab : ∀ j, |b j - a j| ≤ D) :
    |mean x (fun i => x i e) b - mean x (fun i => x i e) a| ≤ D / 2 := by
  apply (response_bound x hx r hfixed hneg a b e).trans
  have hn : ‖b - a‖ ≤ D := (pi_norm_le_iff_of_nonneg hD).mpr hab
  linarith

end Problem336.GibbsField

end

end OAI
