import OAI.Analysis.LipschitzHilbert.Estimates.NestedAverage

namespace OAI

/-! The cellwise weighted averaging step in §10. -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

variable {α κ : Type*} [MeasurableSpace α]

/-- A nonnegative factor of average at most one may be integrated against
a weight comparable to a constant, with the same comparison loss. -/
theorem weighted_average_le (μ : Measure α) [IsFiniteMeasure μ]
    (w f : α → ℝ) {c C : ℝ} (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hw : AEStronglyMeasurable w μ) (hf : Integrable f μ)
    (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x)
    (hlower : ∀ᵐ x ∂μ, c ≤ w x)
    (hupper : ∀ᵐ x ∂μ, w x ≤ C * c)
    (haverage : (∫ x, f x ∂μ) ≤ μ.real Set.univ) :
    Integrable (fun x => w x * f x) μ ∧
      (∫ x, w x * f x ∂μ) ≤ C * ∫ x, w x ∂μ := by
  have hw0 : ∀ᵐ x ∂μ, 0 ≤ w x := hlower.mono fun _ hx => hc.trans hx
  have hwint : Integrable w μ := (integrable_const (C * c)).mono' hw (by
    filter_upwards [hw0, hupper] with x hx0 hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg hx0] using hx)
  have hprod : Integrable (fun x => w x * f x) μ :=
    (hf.const_mul (C * c)).mono' (hw.mul hf.aestronglyMeasurable) (by
      filter_upwards [hw0, hf0, hupper] with x hx0 hf0x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hx0 hf0x)]
      exact mul_le_mul_of_nonneg_right hx hf0x)
  have hlowint : c * μ.real Set.univ ≤ ∫ x, w x ∂μ := by
    simpa only [integral_const, smul_eq_mul, mul_comm] using
      integral_mono_ae (integrable_const c) hwint hlower
  refine ⟨hprod, ?_⟩
  calc
    (∫ x, w x * f x ∂μ) ≤ ∫ x, (C * c) * f x ∂μ :=
      integral_mono_ae hprod (hf.const_mul _) (by
        filter_upwards [hf0, hupper] with x hx0 hx
        exact mul_le_mul_of_nonneg_right hx hx0)
    _ = (C * c) * ∫ x, f x ∂μ := integral_const_mul _ _
    _ ≤ (C * c) * μ.real Set.univ :=
      mul_le_mul_of_nonneg_left haverage (mul_nonneg hC hc)
    _ = C * (c * μ.real Set.univ) := mul_assoc _ _ _
    _ ≤ C * ∫ x, w x ∂μ := mul_le_mul_of_nonneg_left hlowint hC

/-- The actual product of nested normalized predictions admits the same
weighted cell estimate. -/
theorem weighted_nested_average_le [Fintype κ]
    (μ : Measure α) [IsFiniteMeasure μ]
    (P : ℕ → α → κ) (R : ℕ → κ → κ) (g : ℕ → κ → ℝ)
    (N : ℕ) (w : α → ℝ) {c C : ℝ} (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hw : AEStronglyMeasurable w μ)
    (hlower : ∀ᵐ x ∂μ, c ≤ w x) (hupper : ∀ᵐ x ∂μ, w x ≤ C * c)
    (hP : ∀ n ≤ N, ∀ i, MeasurableSet {x | P n x = i})
    (hrefine : ∀ n < N, ∀ x, P n x = R n (P (n + 1) x))
    (hg : ∀ n < N, ∀ i, 0 ≤ g n i)
    (haverage : ∀ n < N, ∀ i,
      (∫ x in {x | P n x = i}, g n (P (n + 1) x) ∂μ) ≤ μ.real {x | P n x = i}) :
    Integrable (fun x => w x * ∏ j ∈ Finset.range N, g j (P (j + 1) x)) μ ∧
      (∫ x, w x * ∏ j ∈ Finset.range N, g j (P (j + 1) x) ∂μ) ≤
        C * ∫ x, w x ∂μ := by
  apply weighted_average_le μ w _ hc hC hw
    (integrable_nested_product μ P R g N (hP N le_rfl) hrefine)
    (Filter.Eventually.of_forall fun x => Finset.prod_nonneg fun j hj =>
      hg j (Finset.mem_range.mp hj) (P (j + 1) x)) hlower hupper
  exact nested_average_product_le μ P R g N hP hrefine hg haverage

end LipschitzHilbert

end

end OAI
