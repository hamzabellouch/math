import OAI.Geometry.RCD.Metric.RadonProductL2Bound
import OAI.Geometry.RCD.Sobolev.ShiftedBochnerMeasure

namespace OAI

/-! # Integrating shifted density bounds without discarding singular mass -/

open Set Filter MeasureTheory

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

/-- A density bound with a constant shift is integrated against the full
positive measure. Its singular part is retained in the upper bound. -/
theorem memLp_two_of_sq_le_shifted_radon (σ : Measure X) [IsFiniteMeasure σ]
    {S : Set X} [IsFiniteMeasure (μ.restrict S)] {f : X → ℝ}
    (hf : AEStronglyMeasurable f (μ.restrict S))
    (c B : ℝ) (hB : 0≤B)
    (hbound : ∀ᵐ x ∂μ.restrict S, (f x)^2≤B*((σ.rnDeriv μ x).toReal-c)) :
    MemLp f 2 (μ.restrict S) ∧
      (∫ x in S, (f x)^2 ∂μ)≤B*(σ.real S-c*μ.real S) := by
  have hd : Integrable (fun x => (σ.rnDeriv μ x).toReal) (μ.restrict S) :=
    Measure.integrableOn_toReal_rnDeriv (μ := σ) (ν := μ) (measure_ne_top σ S)
  have hmajor := (hd.sub (integrable_const c)).const_mul B
  have hi : Integrable (fun x => (f x)^2) (μ.restrict S) := by
    apply hmajor.mono' (hf.pow 2)
    filter_upwards [hbound] with x hx
    simpa only [Pi.pow_apply,Pi.sub_apply,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (f x))] using hx
  refine ⟨(memLp_two_iff_integrable_sq hf).mpr hi,?_⟩
  calc
    (∫ x in S, (f x)^2 ∂μ) ≤ ∫ x in S, B*((σ.rnDeriv μ x).toReal-c) ∂μ :=
      integral_mono_ae hi hmajor hbound
    _ = B*((∫ x in S, (σ.rnDeriv μ x).toReal ∂μ)-c*μ.real S) := by
      rw [integral_const_mul,integral_sub hd (integrable_const c)]
      simp only [integral_const,smul_eq_mul,measureReal_restrict_apply_univ,mul_comm]
    _ ≤ B*(σ.real S-c*μ.real S) := mul_le_mul_of_nonneg_left
      (sub_le_sub_right (Measure.setIntegral_toReal_rnDeriv_le
        (μ := σ) (ν := μ) (measure_ne_top σ S)) _) hB

/-- The mixed estimate permits separate caps on both gradient lengths. -/
theorem memLp_two_of_shifted_radon_product (σ : Measure X) [IsFiniteMeasure σ]
    {S : Set X} [IsFiniteMeasure (μ.restrict S)] {f g h : X → ℝ}
    (hf : AEStronglyMeasurable f (μ.restrict S)) (c C D : ℝ)
    (hC : 0≤C) (hD : 0≤D)
    (hden : ∀ᵐ x ∂μ.restrict S, c≤(σ.rnDeriv μ x).toReal)
    (hg : ∀ᵐ x ∂μ.restrict S, 0≤g x ∧ g x≤C)
    (hh : ∀ᵐ x ∂μ.restrict S, 0≤h x ∧ h x≤D)
    (hbound : ∀ᵐ x ∂μ.restrict S,
      (f x)^2≤((σ.rnDeriv μ x).toReal-c)*g x*h x) :
    MemLp f 2 (μ.restrict S) ∧
      (∫ x in S, (f x)^2 ∂μ)≤(C*D)*(σ.real S-c*μ.real S) := by
  apply memLp_two_of_sq_le_shifted_radon μ σ hf c (C*D) (mul_nonneg hC hD)
  filter_upwards [hden,hg,hh,hbound] with x hd hg hh hb
  calc
    (f x)^2 ≤ ((σ.rnDeriv μ x).toReal-c)*g x*h x := hb
    _ = ((σ.rnDeriv μ x).toReal-c)*(g x*h x) := mul_assoc _ _ _
    _ ≤ ((σ.rnDeriv μ x).toReal-c)*(C*D) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hg.2 hh.2 hh.1 hC) (sub_nonneg.mpr hd)
    _ = _ := mul_comm _ _

/-- A local lower bound for the absolutely continuous density bounds the
full positive mass on every measurable subset, for either sign of c. -/
theorem measure_lower_of_radon_lower (σ : Measure X) [IsFiniteMeasure σ]
    {Ω : Set X} [IsFiniteMeasure (μ.restrict Ω)]
    (c : ℝ) (hc : ∀ᵐ x ∂μ.restrict Ω, c≤(σ.rnDeriv μ x).toReal)
    (s : Set X) (hs : MeasurableSet s) :
    c*(μ.restrict Ω).real s≤σ.real s := by
  by_cases hneg : c≤0
  · exact (mul_nonpos_of_nonpos_of_nonneg hneg ENNReal.toReal_nonneg).trans ENNReal.toReal_nonneg
  have hi : IsFiniteMeasure (μ.restrict (s∩Ω)) := by
    rw [← Measure.restrict_restrict hs]
    infer_instance
  have hcs : ∀ᵐ x ∂μ.restrict (s∩Ω), c≤(σ.rnDeriv μ x).toReal :=
    ae_restrict_of_ae_restrict_of_subset inter_subset_right hc
  have hd : Integrable (fun x => (σ.rnDeriv μ x).toReal) (μ.restrict (s∩Ω)) :=
    Measure.integrableOn_toReal_rnDeriv (μ := σ) (ν := μ) (measure_ne_top σ (s∩Ω))
  rw [measureReal_restrict_apply hs]
  calc
    c*μ.real (s∩Ω) = ∫ _x in s∩Ω, c ∂μ := by
      simp only [integral_const,smul_eq_mul,measureReal_restrict_apply_univ,mul_comm]
    _ ≤ ∫ x in s∩Ω, (σ.rnDeriv μ x).toReal ∂μ := integral_mono_ae (integrable_const _) hd hcs
    _ ≤ σ.real (s∩Ω) := Measure.setIntegral_toReal_rnDeriv_le (measure_ne_top σ (s∩Ω))
    _ ≤ σ.real s := measureReal_mono inter_subset_left

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- The local density consequence of the finite-dimensional inequality
constructs positivity of the full shifted measure. -/
theorem shiftedBochnerLowerBound_of_density (M : PositiveBilinearMeasure X E)
    {Ω : Set X} [IsFiniteMeasure (μ.restrict Ω)]
    (ell : E →ₗ[ℝ] ℝ) (n : ℝ)
    (hd : ∀ v b, ∀ᵐ x ∂μ.restrict Ω,
      2*b*ell v-n*b^2≤((M.measure v).rnDeriv μ x).toReal) :
    ShiftedBochnerLowerBound M (μ.restrict Ω) ell n := by
  intro v b s hs
  exact measure_lower_of_radon_lower μ (M.measure v) _ (hd v b) s hs

end RegularPointCoordinates

end

end OAI
