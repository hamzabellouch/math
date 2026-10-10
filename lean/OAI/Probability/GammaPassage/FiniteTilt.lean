import OAI.Probability.GammaPassage.TiltMoment
import OAI.Probability.GammaPassage.ScalingLaw
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Constructions.Pi

namespace OAI

namespace GammaFPP

open Set Finset MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {ι : Type*} [Fintype ι]

/-- The iid Gamma law on a finite set of coordinates. -/
noncomputable def finiteGammaMeasure (shape rate : ℝ) : Measure (ι → ℝ) :=
  Measure.pi (fun _ : ι => gammaMeasure shape rate)

/-- Product likelihood for coordinatewise scaling by `a`. -/
noncomputable def finiteGammaScaleLikelihood (shape rate a : ℝ) (x : ι → ℝ) : ℝ≥0∞ :=
  ∏ i, ENNReal.ofReal (gammaScaleLikelihood shape rate a (x i))

lemma measurable_finiteGammaScaleLikelihood (shape rate a : ℝ) :
    Measurable (finiteGammaScaleLikelihood (ι := ι) shape rate a) := by
  unfold finiteGammaScaleLikelihood gammaScaleLikelihood
  fun_prop

/-- Factorization of nonnegative integrals under a finite product of probability measures. -/
private theorem probability_pi_lintegral_prod (μ : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (f : ι → ℝ → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ) = ∏ i, ∫⁻ y, f i y ∂μ i := by
  have hi : iIndepFun (fun i (x : ι → ℝ) => f i (x i)) (Measure.pi μ) :=
    iIndepFun_pi (fun i => (hf i).aemeasurable)
  have hh := lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ _ hi
    (fun i => (hf i).comp (measurable_pi_apply i))
  rw [hh]
  apply Finset.prod_congr rfl
  intro i _
  rw [← lintegral_map (hf i) (measurable_pi_apply i), (measurePreserving_eval μ i).map_eq]

private theorem indicator_pi_prod (s : ι → Set ℝ) (f : ι → ℝ → ℝ≥0∞)
    (x : ι → ℝ) :
    (Set.univ.pi s).indicator (fun y => ∏ i, f i (y i)) x =
      ∏ i, (s i).indicator (f i) (x i) := by
  classical
  by_cases hx : ∀ i, x i ∈ s i
  · have hh : x ∈ Set.univ.pi s := by simpa using hx
    rw [Set.indicator_of_mem hh]
    apply Finset.prod_congr rfl
    intro i _
    rw [Set.indicator_of_mem (hx i)]
  · obtain ⟨i, hi⟩ := not_forall.mp hx
    have hh : x ∉ Set.univ.pi s := by simpa using (not_forall.mpr ⟨i, hi⟩)
    rw [Set.indicator_of_notMem hh]
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)

/-- Coordinatewise Gamma likelihoods change the rate in the product measure. -/
theorem finite_gamma_withDensity_scale {shape rate a : ℝ}
    (hs : 0 < shape) (hr : 0 < rate) (ha : 0 < a) :
    (finiteGammaMeasure (ι := ι) shape rate).withDensity
        (finiteGammaScaleLikelihood shape rate a) =
      finiteGammaMeasure shape (rate / a) := by
  let : IsProbabilityMeasure (gammaMeasure shape rate) :=
    isProbabilityMeasure_gammaMeasure hs hr
  let : IsProbabilityMeasure (gammaMeasure shape (rate / a)) :=
    isProbabilityMeasure_gammaMeasure hs (div_pos hr ha)
  unfold finiteGammaMeasure
  symm
  apply Measure.pi_eq
  intro s hsmeas
  rw [withDensity_apply _ (MeasurableSet.univ_pi hsmeas),
    ← lintegral_indicator (MeasurableSet.univ_pi hsmeas)]
  change (∫⁻ x, (Set.univ.pi s).indicator
    (fun y => ∏ i, ENNReal.ofReal (gammaScaleLikelihood shape rate a (y i))) x
    ∂Measure.pi (fun _ : ι => gammaMeasure shape rate)) = _
  simp_rw [indicator_pi_prod s (fun _ x => ENNReal.ofReal (gammaScaleLikelihood shape rate a x))]
  rw [probability_pi_lintegral_prod _
    (fun i => (s i).indicator (fun x => ENNReal.ofReal (gammaScaleLikelihood shape rate a x)))
    (fun i => (by unfold gammaScaleLikelihood; fun_prop :
      Measurable (fun x => ENNReal.ofReal (gammaScaleLikelihood shape rate a x))).indicator (hsmeas i))]
  apply Finset.prod_congr rfl
  intro i _
  rw [lintegral_indicator (hsmeas i), ← withDensity_apply _ (hsmeas i),
    gammaMeasure_withDensity_scaleLikelihood hs hr ha]

/-- The pushforward of a finite Gamma law under coordinatewise scaling. -/
theorem finite_gamma_map_scale {shape rate a : ℝ}
    (hs : 0 < shape) (hr : 0 < rate) (ha : 0 < a) :
    (finiteGammaMeasure (ι := ι) shape rate).map (fun x i => a * x i) =
      finiteGammaMeasure shape (rate / a) := by
  let : IsProbabilityMeasure (gammaMeasure shape rate) :=
    isProbabilityMeasure_gammaMeasure hs hr
  let : ∀ _ : ι, IsProbabilityMeasure
      ((gammaMeasure shape rate).map (fun x : ℝ => a * x)) :=
    fun _ => inferInstance
  unfold finiteGammaMeasure
  rw [Measure.pi_map_pi
    (fun _ => (by fun_prop : Measurable (fun x : ℝ => a * x)).aemeasurable)]
  simp only [map_mul_gammaMeasure hs hr ha]

/-- The scaling pushforward equals the measure weighted by the product likelihood. -/
theorem finite_gamma_map_scale_eq_withDensity {shape rate a : ℝ}
    (hs : 0 < shape) (hr : 0 < rate) (ha : 0 < a) :
    (finiteGammaMeasure (ι := ι) shape rate).map (fun x i => a * x i) =
      (finiteGammaMeasure shape rate).withDensity
        (finiteGammaScaleLikelihood shape rate a) := by
  rw [finite_gamma_map_scale hs hr ha, finite_gamma_withDensity_scale hs hr ha]

/-- The second moment of the product likelihood factors over the coordinates. -/
theorem finite_gamma_shrink_second_moment_pow {shape rate delta : ℝ}
    (hs : 0 < shape) (hr : 0 < rate) (hlo : -1 < delta) (hhi : delta < 1) :
    (∫⁻ x, (finiteGammaScaleLikelihood (ι := ι) shape rate (1 - delta) x) ^ 2
      ∂finiteGammaMeasure shape rate) =
      (ENNReal.ofReal ((1 - delta ^ 2) ^ (-shape))) ^ Fintype.card ι := by
  let : IsProbabilityMeasure (gammaMeasure shape rate) :=
    isProbabilityMeasure_gammaMeasure hs hr
  simp only [finiteGammaMeasure, finiteGammaScaleLikelihood, ← Finset.prod_pow]
  rw [probability_pi_lintegral_prod _
    (fun _ x => (ENNReal.ofReal (gammaScaleLikelihood shape rate (1 - delta) x)) ^ 2)
    (fun _ => by unfold gammaScaleLikelihood; fun_prop)]
  change (∏ _ : ι, ∫⁻ x, (ENNReal.ofReal (gammaShrinkLikelihood shape rate delta x)) ^ 2
    ∂gammaMeasure shape rate) = _
  simp only [gamma_shrink_likelihood_second_lintegral hs hr hlo hhi,
    Finset.prod_const, Finset.card_univ]

/-- The second moment is `(1 - delta²)^(-shape * N)` for `-1 < delta < 1`, including `N = 0`. -/
theorem finite_gamma_shrink_second_moment {shape rate delta : ℝ}
    (hs : 0 < shape) (hr : 0 < rate) (hlo : -1 < delta) (hhi : delta < 1) :
    (∫⁻ x, (finiteGammaScaleLikelihood (ι := ι) shape rate (1 - delta) x) ^ 2
      ∂finiteGammaMeasure shape rate) =
      ENNReal.ofReal ((1 - delta ^ 2) ^ (-shape * (Fintype.card ι : ℝ))) := by
  have hb : 0 < 1 - delta ^ 2 := by
    have hprod : 0 < (1 - delta) * (1 + delta) :=
      mul_pos (sub_pos.mpr hhi) (by linarith)
    nlinarith
  rw [finite_gamma_shrink_second_moment_pow hs hr hlo hhi,
    Real.rpow_mul_natCast hb.le (-shape) (Fintype.card ι)]
  exact (ENNReal.ofReal_pow (Real.rpow_nonneg hb.le (-shape)) (Fintype.card ι)).symm

end GammaFPP

end OAI
