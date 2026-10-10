import OAI.GroupTheory.PolycyclicRecognition.Algebra.AutocorrelationRecurrence
import OAI.GroupTheory.PolycyclicRecognition.Analysis.RecurrenceIntegralBounds

namespace OAI

/-! # The quantitative lower bound for a two-sample return -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set Filter
open scoped ENNReal

/-- A function with values in `[0,1]`, supported in a finite-volume region,
has square integral at least its squared mass divided by that volume. -/
theorem sq_mass_le_region_mul_square_mass
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f : X → ℝ≥0∞) (hf : Measurable f) (hb : ∀ x, f x ≤ 1)
    (R : Set X) (hRfin : μ R ≠ ∞) (hRpos : 0 < (μ R).toReal)
    (hsupp : ∀ x, x ∉ R → f x = 0) :
    (∫⁻ x, f x ∂μ).toReal ^ 2 ≤ (μ R).toReal * (∫⁻ x, f x ^ 2 ∂μ).toReal := by
  let ν := μ.restrict R
  let : IsFiniteMeasure ν := ⟨by simpa only [ν, Measure.restrict_apply_univ] using hRfin.lt_top⟩
  have hfn (x : X) : f x ≠ ∞ := (hb x).trans_lt (by simp) |>.ne
  have hr (x : X) : 0 ≤ (f x).toReal ∧ (f x).toReal ≤ 1 :=
    ⟨ENNReal.toReal_nonneg, by simpa using ENNReal.toReal_mono (by simp) (hb x)⟩
  have hfi : Integrable (fun x => (f x).toReal) ν :=
    Integrable.of_bound hf.ennreal_toReal.aestronglyMeasurable 1
      (Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hr x).1]
        exact (hr x).2))
  have hfi2 : Integrable (fun x => (f x).toReal ^ 2) ν :=
    Integrable.of_bound (hf.ennreal_toReal.pow_const 2).aestronglyMeasurable 1
      (Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        nlinarith [(hr x).1, (hr x).2]))
  have hregion : Function.support f ⊆ R := by
    intro x hx
    by_contra hn
    exact hx (hsupp x hn)
  have hregion2 : Function.support (fun x => f x ^ 2) ⊆ R := by
    intro x hx
    by_contra hn
    exact hx (by simp [hsupp x hn])
  have hI : (∫ x, (f x).toReal ∂ν) = (∫⁻ x, f x ∂μ).toReal := by
    rw [integral_toReal hf.aemeasurable (Eventually.of_forall (fun x => (hfn x).lt_top))]
    congr 1
    exact setLIntegral_eq_of_support_subset hregion
  have hI2 : (∫ x, (f x).toReal ^ 2 ∂ν) = (∫⁻ x, f x ^ 2 ∂μ).toReal := by
    simp_rw [← ENNReal.toReal_pow]
    rw [integral_toReal (hf.pow_const 2).aemeasurable
      (Eventually.of_forall (fun x => by exact ENNReal.pow_ne_top (hfn x) |>.lt_top))]
    congr 1
    exact setLIntegral_eq_of_support_subset hregion2
  have h := sq_integral_le_mass_mul_integral_sq ν
    (by simpa only [measureReal_def, ν, Measure.restrict_apply_univ] using hRpos)
    (fun x => (f x).toReal) hfi hfi2
  simpa only [hI, hI2, measureReal_def, ν, Measure.restrict_apply_univ] using h

/-- The mean probability of returning to `A` after a difference of two
independent increments has the required quadratic lower bound. The region
`R` can be the compact product `Q * support σ` in the application. -/
theorem return_correlation_lower_bound
    {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (μ σ : Measure G) [SFinite μ] [IsProbabilityMeasure σ] [μ.IsMulRightInvariant]
    (A K R : Set G) (hA : MeasurableSet A) (hK : ∀ᵐ s ∂σ, s ∈ K)
    (hRfin : μ R ≠ ∞) (hRpos : 0 < (μ R).toReal)
    (hAR : ∀ a ∈ A, ∀ s ∈ K, a * s ∈ R) :
    (μ A).toReal ^ 2 ≤ (μ R).toReal *
      (∫⁻ x in A, ∫⁻ s₁, ∫⁻ s₂,
        A.indicator (fun _ => (1 : ℝ≥0∞)) (x * s₁ * s₂⁻¹) ∂σ ∂σ ∂μ).toReal := by
  let f := A.indicator (fun _ => (1 : ℝ≥0∞))
  have hf : Measurable f := measurable_const.indicator hA
  have hb : ∀ x, f x ≤ 1 := indicator_le_self' (fun _ _ => bot_le)
  have h := sq_mass_le_region_mul_square_mass μ (rightInverseAverage σ f)
    (measurable_rightInverseAverage σ hf) (rightInverseAverage_le_one σ hb)
    R hRfin hRpos (fun x hx => rightInverseAverage_indicator_eq_zero σ A K R hK hAR hx)
  rw [lintegral_rightInverseAverage μ σ f hf, lintegral_indicator_const hA, one_mul,
    ← right_autocorrelation_eq_square μ σ f hf] at h
  have heq : (fun x => f x * (∫⁻ s, rightInverseAverage σ f (x * s) ∂σ)) =
      A.indicator (fun x => ∫⁻ s₁, ∫⁻ s₂, f (x * s₁ * s₂⁻¹) ∂σ ∂σ) := by
    funext x
    by_cases hx : x ∈ A <;> simp [f, hx, rightInverseAverage]
  rw [heq, lintegral_indicator hA] at h
  exact h

end PolycyclicRecognition

end

end OAI
