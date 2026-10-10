import OAI.Geometry.RCD.Sobolev.RawCutoffError

namespace OAI

/-! # Local and global cutoff error comparisons -/

open Set MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

omit [ProperSpace X] in
/-- A cutoff between zero and one only decreases a local directional error. -/
theorem cutoff_error_on_le (u : SobolevSpace μ hQ) (c : ℝ) (s : Set X) (hs : μ s ≠ ∞)
    {χ : X → ℝ} (hχ : AEStronglyMeasurable χ μ)
    (hχrange : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) :
    (∫ x in s, χ x * |localGamma μ hQ u u x - c| ∂μ) ≤
      ∫ x in s, |localGamma μ hQ u u x - c| ∂μ := by
  have hi : IntegrableOn (fun x => |localGamma μ hQ u u x - c|) s μ :=
    ((localGamma_memL1 μ hQ u u).integrableOn.sub (integrableOn_const hs)).abs
  have hb : ∀ᵐ x ∂μ.restrict s, ‖χ x‖ ≤ ((1 : ℝ≥0) : ℝ) :=
    Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hχrange x).1]
      exact (hχrange x).2
  apply integral_mono_ae (hi.bdd_mul hχ.restrict hb) hi
  exact Filter.Eventually.of_forall fun x => mul_le_of_le_one_left (abs_nonneg _) (hχrange x).2

omit [ProperSpace X] in
/-- Finite support measure suffices for integrability of the cutoff error. -/
theorem cutoff_error_integrable_of_finite_region (u : SobolevSpace μ hQ) (c : ℝ)
    {s : Set X} (hs : μ s ≠ ∞) {χ : X → ℝ}
    (hχ : AEStronglyMeasurable χ μ) (hχrange : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (hχzero : ∀ x ∉ s, χ x = 0) :
    Integrable (fun x => χ x * |localGamma μ hQ u u x - c|) μ := by
  have hb : ∀ᵐ x ∂μ, ‖χ x‖ ≤ ((1 : ℝ≥0) : ℝ) :=
    Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hχrange x).1]
      exact (hχrange x).2
  have hsupp : Function.support χ ⊆ s := by
    intro x hx
    by_contra hn
    exact hx (hχzero x hn)
  have hi : Integrable χ μ := (integrableOn_iff_integrable_of_support_subset hsupp).mp
    ((integrableOn_const hs (C := (1 : ℝ))).mono' hχ.restrict (ae_restrict_of_ae hb))
  exact weighted_direction_error_integrable μ hQ u c hχ hb hi
    (Filter.Eventually.of_forall fun x => (hχrange x).1)

omit [ProperSpace X] in
/-- Every local portion of a cutoff error is bounded by its total error. -/
theorem cutoff_error_on_le_total (u : SobolevSpace μ hQ) (c : ℝ)
    {s : Set X} (hs : μ s ≠ ∞) {χ : X → ℝ}
    (hχ : AEStronglyMeasurable χ μ) (hχrange : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (hχzero : ∀ x ∉ s, χ x = 0) (t : Set X) :
    (∫ x in t, χ x * |localGamma μ hQ u u x - c| ∂μ) ≤
      ∫ x, χ x * |localGamma μ hQ u u x - c| ∂μ :=
  setIntegral_le_integral
    (cutoff_error_integrable_of_finite_region μ hQ u c hs hχ hχrange hχzero)
    (Filter.Eventually.of_forall fun x => mul_nonneg (hχrange x).1 (abs_nonneg _))

end RegularPointCoordinates

end

end OAI
