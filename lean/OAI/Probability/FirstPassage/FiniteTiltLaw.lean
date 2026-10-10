import OAI.Probability.FirstPassage.ExponentialTiltLaw
import Mathlib.Probability.Independence.Integration

namespace OAI

namespace PlanarFPP
open Set Finset MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {ι : Type*} [Fintype ι]

theorem probability_pi_lintegral_prod (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (f : ι → ℝ → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ)=∏ i, ∫⁻ y, f i y ∂μ i := by
  have hi : iIndepFun (fun i (x : ι → ℝ) => f i (x i)) (Measure.pi μ) :=
    iIndepFun_pi (fun i => (hf i).aemeasurable)
  have hh := lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ _ hi
    (fun i => (hf i).comp (measurable_pi_apply i))
  rw [hh]
  apply Finset.prod_congr rfl
  intro i _
  rw [← lintegral_map (hf i) (measurable_pi_apply i), (measurePreserving_eval μ i).map_eq]

theorem indicator_pi_prod (s : ι → Set ℝ) (f : ι → ℝ → ℝ≥0∞) (x : ι → ℝ) :
    (Set.univ.pi s).indicator (fun y => ∏ i, f i (y i)) x =
      ∏ i, (s i).indicator (f i) (x i) := by
  classical
  by_cases hx : ∀ i, x i ∈ s i
  · have hh : x ∈ Set.univ.pi s := by simpa using hx
    rw [Set.indicator_of_mem hh]
    apply Finset.prod_congr rfl
    intro i _
    rw [Set.indicator_of_mem (hx i)]
  · obtain ⟨i,hi⟩ := not_forall.mp hx
    have hh : x ∉ Set.univ.pi s := by simpa using (not_forall.mpr ⟨i,hi⟩)
    rw [Set.indicator_of_notMem hh]
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)

noncomputable def finiteExponentialLikelihood (ρ : ℝ) (x : ι → ℝ) : ℝ≥0∞ :=
  ∏ i, ENNReal.ofReal (exponentialLikelihood ρ (x i))

theorem measurable_finiteExponentialLikelihood (ρ : ℝ) :
    Measurable (finiteExponentialLikelihood (ι := ι) ρ) := by
  unfold finiteExponentialLikelihood exponentialLikelihood
  fun_prop

theorem finite_expMeasure_withDensity (ρ : ℝ) (hρ : 0 < ρ) :
    (Measure.pi (fun _ : ι => expMeasure 1)).withDensity (finiteExponentialLikelihood ρ)=
      Measure.pi (fun _ : ι => expMeasure ρ) := by
  let _ := isProbabilityMeasure_expMeasure hρ
  symm
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),← lintegral_indicator (MeasurableSet.univ_pi hs)]
  change (∫⁻ x, (Set.univ.pi s).indicator (fun y => ∏ i, ENNReal.ofReal (exponentialLikelihood ρ (y i))) x
    ∂Measure.pi (fun _ : ι => expMeasure 1)) = _
  simp_rw [indicator_pi_prod s (fun _ x => ENNReal.ofReal (exponentialLikelihood ρ x))]
  rw [probability_pi_lintegral_prod _ (fun i => (s i).indicator (fun x => ENNReal.ofReal (exponentialLikelihood ρ x))) (fun i =>
    (by unfold exponentialLikelihood; fun_prop : Measurable (fun x => ENNReal.ofReal (exponentialLikelihood ρ x))).indicator (hs i))]
  apply Finset.prod_congr rfl
  intro i _
  rw [lintegral_indicator (hs i),← withDensity_apply _ (hs i),expMeasure_withDensity_likelihood ρ hρ.le]

theorem finite_expMeasure_map_scale (α : ℝ) (hα : 0 < α) :
    (Measure.pi (fun _ : ι => expMeasure 1)).map (fun x i => α*x i)=
      Measure.pi (fun _ : ι => expMeasure (1/α)) := by
  rw [Measure.pi_map_pi (fun _ => (by fun_prop : Measurable (fun x : ℝ => α*x)).aemeasurable)]
  simp only [expMeasure_map_scale α hα]

theorem finite_exponential_likelihood_second_moment (ρ : ℝ) (hρ : 1/2 < ρ) :
    (∫⁻ x, (finiteExponentialLikelihood (ι := ι) ρ x)^2 ∂Measure.pi (fun _ : ι => expMeasure 1))=
      (ENNReal.ofReal (ρ^2/(2*ρ-1)))^(Fintype.card ι) := by
  simp only [finiteExponentialLikelihood,← Finset.prod_pow]
  rw [probability_pi_lintegral_prod _ (fun _ x => (ENNReal.ofReal (exponentialLikelihood ρ x))^2)
    (fun _ => by unfold exponentialLikelihood; fun_prop)]
  simp only [exponential_likelihood_second_moment ρ hρ,Finset.prod_const,Finset.card_univ]

end PlanarFPP

end OAI
