import OAI.Analysis.LipschitzHilbert.Phase.PredictionNormalization
import Mathlib.MeasureTheory.Group.Arithmetic

namespace OAI

/-! Accumulating pointwise prediction errors without a loss per level. -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

variable {ι α : Type*} [Fintype ι] [MeasurableSpace α]

omit [MeasurableSpace α] in
theorem product_le_exp_sum (β γ e : ι → ℝ) (hβ : ∀ i, 0 ≤ β i)
    (hcomparison : ∀ i, β i ≤ Real.exp (e i) * γ i) :
    (∏ i, β i) ≤ Real.exp (∑ i, e i) * ∏ i, γ i := by
  calc
    _ ≤ ∏ i, Real.exp (e i) * γ i := Finset.prod_le_prod₀
      (fun i _ => hβ i) (fun i _ => hcomparison i)
    _ = _ := by rw [Finset.prod_mul_distrib, Real.exp_sum]

omit [MeasurableSpace α] in
theorem product_le_of_error_budget (β γ e : ι → ℝ) (B : ℝ)
    (hβ : ∀ i, 0 ≤ β i) (hγ : ∀ i, 0 ≤ γ i)
    (hcomparison : ∀ i, β i ≤ Real.exp (e i) * γ i) (hbudget : ∑ i, e i ≤ B) :
    (∏ i, β i) ≤ Real.exp B * ∏ i, γ i :=
  (product_le_exp_sum β γ e hβ hcomparison).trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hbudget)
      (Finset.prod_nonneg (fun i _ => hγ i)))

theorem integrable_perturbed_product (μ : Measure α)
    (β γ e : ι → α → ℝ) (B : ℝ)
    (hβmeas : ∀ i, Measurable (β i)) (hγint : Integrable (fun x => ∏ i, γ i x) μ)
    (hβ : ∀ᵐ x ∂μ, ∀ i, 0 ≤ β i x) (hγ : ∀ᵐ x ∂μ, ∀ i, 0 ≤ γ i x)
    (hcomparison : ∀ᵐ x ∂μ, ∀ i, β i x ≤ Real.exp (e i x) * γ i x)
    (hbudget : ∀ᵐ x ∂μ, ∑ i, e i x ≤ B) :
    Integrable (fun x => ∏ i, β i x) μ := by
  have hmeas : Measurable (fun x => ∏ i, β i x) :=
    Finset.measurable_prod Finset.univ (fun i _ => hβmeas i)
  apply (hγint.const_mul (Real.exp B)).mono' hmeas.aestronglyMeasurable
  filter_upwards [hβ, hγ, hcomparison, hbudget] with x hbx hgx hcx hex
  rw [Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg (fun i _ => hbx i))]
  exact product_le_of_error_budget (fun i => β i x) (fun i => γ i x) (fun i => e i x)
    B hbx hgx hcx hex

theorem integral_perturbed_product_le (μ : Measure α)
    (β γ e : ι → α → ℝ) (A B : ℝ)
    (hβmeas : ∀ i, Measurable (β i)) (hγint : Integrable (fun x => ∏ i, γ i x) μ)
    (hβ : ∀ᵐ x ∂μ, ∀ i, 0 ≤ β i x) (hγ : ∀ᵐ x ∂μ, ∀ i, 0 ≤ γ i x)
    (hcomparison : ∀ᵐ x ∂μ, ∀ i, β i x ≤ Real.exp (e i x) * γ i x)
    (hbudget : ∀ᵐ x ∂μ, ∑ i, e i x ≤ B)
    (haverage : (∫ x, ∏ i, γ i x ∂μ) ≤ A) :
    (∫ x, ∏ i, β i x ∂μ) ≤ Real.exp B * A := by
  have hi := integrable_perturbed_product μ β γ e B hβmeas hγint hβ hγ hcomparison hbudget
  calc
    _ ≤ ∫ x, Real.exp B * ∏ i, γ i x ∂μ := by
      apply integral_mono_ae hi (hγint.const_mul _)
      filter_upwards [hβ, hγ, hcomparison, hbudget] with x hbx hgx hcx hex
      exact product_le_of_error_budget (fun i => β i x) (fun i => γ i x) (fun i => e i x)
        B hbx hgx hcx hex
    _ = Real.exp B * ∫ x, ∏ i, γ i x ∂μ := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left haverage (Real.exp_pos B).le

end LipschitzHilbert

end

end OAI
