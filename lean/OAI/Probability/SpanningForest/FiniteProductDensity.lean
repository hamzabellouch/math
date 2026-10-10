import OAI.Probability.SpanningForest.GaussianLikelihood

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace Problem336.GaussianObservation

theorem pi_withDensity_of_probability {ι : Type*} [Fintype ι]
    {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (μ ν : (i : ι) → Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
    [∀ i, SigmaFinite (ν i)] (f : (i : ι) → α i → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) (hν : ∀ i, ν i = (μ i).withDensity (f i)) :
    Measure.pi ν = (Measure.pi μ).withDensity (fun y => ∏ i, f i (y i)) := by
  classical
  apply Measure.pi_eq
  intro s hs
  have hrect := MeasurableSet.univ_pi hs
  have hind : (Set.univ.pi s).indicator (fun y => ∏ i, f i (y i)) =
      (fun y => ∏ i, (s i).indicator (f i) (y i)) := by
    funext y
    by_cases hy : ∀ i, y i ∈ s i
    · rw [Set.indicator_of_mem (by simpa only [Set.mem_univ_pi] using hy)]
      apply Finset.prod_congr rfl
      intro i hi
      exact (Set.indicator_of_mem (hy i) (f i)).symm
    · rw [Set.indicator_of_notMem (by simpa only [Set.mem_univ_pi] using hy)]
      obtain ⟨i, hi⟩ := not_forall.mp hy
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi (f i))
  rw [withDensity_apply _ hrect, ← lintegral_indicator hrect, hind]
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ
    (fun i (y : ∀ j, α j) => (s i).indicator (f i) (y i))
    (iIndepFun_pi (fun i => ((hf i).indicator (hs i)).aemeasurable))
    (fun i => ((hf i).indicator (hs i)).comp (measurable_pi_apply i))]
  apply Finset.prod_congr rfl
  intro i hi
  rw [(measurePreserving_eval μ i).lintegral_comp ((hf i).indicator (hs i)),
    lintegral_indicator (hs i), hν i, withDensity_apply _ (hs i)]

theorem gaussian_pi_binary_shift_withDensity {ι : Type*} [Fintype ι]
    (v : ℝ≥0) (hv : v ≠ 0) (x : ι → ℝ) (hx : ∀ i, x i = 0 ∨ x i = 1) :
    Measure.pi (fun i => gaussianReal ((v : ℝ) * x i) v) =
      (Measure.pi (fun _ : ι => gaussianReal 0 v)).withDensity
        (fun y => ENNReal.ofReal (Real.exp (∑ i, (y i - (v : ℝ) / 2) * x i))) := by
  have h := pi_withDensity_of_probability
    (fun _ : ι => gaussianReal 0 v) (fun i => gaussianReal ((v : ℝ) * x i) v)
    (fun i y => ENNReal.ofReal (Real.exp ((y - (v : ℝ) / 2) * x i)))
    (fun _ => by fun_prop) (fun i => gaussian_binary_shift_withDensity v hv (x i) (hx i))
  simpa only [Real.exp_sum,
    ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le)] using h

theorem gaussian_pi_binary_shift_withDensity_all {ι : Type*} [Fintype ι]
    (v : ℝ≥0) (x : ι → ℝ) (hx : ∀ i, x i = 0 ∨ x i = 1) :
    Measure.pi (fun i => gaussianReal ((v : ℝ) * x i) v) =
      (Measure.pi (fun _ : ι => gaussianReal 0 v)).withDensity
        (fun y => ENNReal.ofReal (Real.exp (∑ i, (y i - (v : ℝ) / 2) * x i))) := by
  have h := pi_withDensity_of_probability
    (fun _ : ι => gaussianReal 0 v) (fun i => gaussianReal ((v : ℝ) * x i) v)
    (fun i y => ENNReal.ofReal (Real.exp ((y - (v : ℝ) / 2) * x i)))
    (fun _ => by fun_prop) (fun i => gaussian_binary_shift_withDensity_all v (x i) (hx i))
  simpa only [Real.exp_sum,
    ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le)] using h

theorem rnDeriv_gaussian_pi_binary_shift {ι : Type*} [Fintype ι]
    (v : ℝ≥0) (hv : v ≠ 0) (x : ι → ℝ) (hx : ∀ i, x i = 0 ∨ x i = 1) :
    (Measure.pi (fun i => gaussianReal ((v : ℝ) * x i) v)).rnDeriv
        (Measure.pi (fun _ : ι => gaussianReal 0 v)) =ᵐ[
          Measure.pi (fun _ : ι => gaussianReal 0 v)]
      (fun y => ENNReal.ofReal (Real.exp (∑ i, (y i - (v : ℝ) / 2) * x i))) := by
  rw [gaussian_pi_binary_shift_withDensity v hv x hx]
  exact Measure.rnDeriv_withDensity _ (by fun_prop)

theorem gaussian_pi_likelihood_lintegral_eq_one {ι : Type*} [Fintype ι]
    (v : ℝ≥0) (hv : v ≠ 0) (x : ι → ℝ) (hx : ∀ i, x i = 0 ∨ x i = 1) :
    (∫⁻ y, ENNReal.ofReal (Real.exp (∑ i, (y i - (v : ℝ) / 2) * x i))
      ∂Measure.pi (fun _ : ι => gaussianReal 0 v)) = 1 := by
  have h := congrArg (fun μ : Measure (ι → ℝ) => μ Set.univ)
    (gaussian_pi_binary_shift_withDensity v hv x hx)
  simpa only [measure_univ, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ] using h.symm

end Problem336.GaussianObservation

end

end OAI
