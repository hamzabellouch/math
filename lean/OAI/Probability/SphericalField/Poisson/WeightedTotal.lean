import Mathlib
import OAI.Probability.SphericalField.Poisson.Superposition

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron
def poissonWeightedTotal {S : Type*} [MeasurableSpace S] (F : S → ℝ)
    (η : Measure (ℝ × S)) : ℝ :=
  (∫⁻ p, ENNReal.ofReal (Real.exp (p.1+F p.2)) ∂η).toReal

lemma poissonWeightedTotal_measurable {S : Type*} [MeasurableSpace S]
    {F : S → ℝ} (hF : Measurable F) : Measurable (poissonWeightedTotal F) :=
  (Measure.measurable_lintegral ((measurable_fst.add (hF.comp measurable_snd)).exp.ennreal_ofReal)).ennreal_toReal

lemma poissonWeightedTotal_eq {S : Type*} [MeasurableSpace S]
    {F : S → ℝ} (hF : Measurable F) (η : Measure (ℝ × S)) :
    poissonWeightedTotal F η = stablePoissonTotal (η.map (fun p => p.1+F p.2)) := by
  unfold poissonWeightedTotal stablePoissonTotal
  rw [lintegral_map (by fun_prop) (by fun_prop)]

lemma poissonWeightedTotal_add_const {S : Type*} [MeasurableSpace S]
    {F : S → ℝ} (_hF : Measurable F) (c : ℝ) (η : Measure (ℝ × S)) :
    poissonWeightedTotal (fun x => F x+c) η = Real.exp c * poissonWeightedTotal F η := by
  unfold poissonWeightedTotal
  simp_rw [show ∀ p : ℝ × S, p.1+(F p.2+c) = c+(p.1+F p.2) by intro p; ring,
    Real.exp_add,ENNReal.ofReal_mul (Real.exp_pos c).le]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.exp_pos c).le]

lemma normalized_mark_density_probability {S : Type*} [MeasurableSpace S]
    (ν : Measure S) {b : ℝ} {F : S → ℝ}
    (hI : Integrable (fun x => Real.exp (b*F x)) ν)
    (hM : (∫ x, Real.exp (b*F x) ∂ν) = 1) :
    IsProbabilityMeasure (ν.withDensity (fun x => ENNReal.ofReal (Real.exp (b*F x)))) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hI (ae_of_all _ fun x => (Real.exp_pos _).le),hM]
  simp

lemma stablePoisson_normalized_mark_projection {S : Type*} [MeasurableSpace S] [Nonempty S]
    (ν : Measure S) [IsProbabilityMeasure ν] {b : ℝ} (hb : 0 ≤ b)
    {F : S → ℝ} (hF : Measurable F)
    (hI : Integrable (fun x => Real.exp (b*F x)) ν)
    (hM : (∫ x, Real.exp (b*F x) ∂ν) = 1) :
    (poissonRandomMeasureLaw ((stableLogIntensity b).prod ν)).map
      (Measure.map (fun p : ℝ × S => p.1+F p.2)) =
        poissonRandomMeasureLaw (stableLogIntensity b) := by
  have : IsProbabilityMeasure (ν.withDensity (fun x => ENNReal.ofReal (Real.exp (b*F x)))) :=
    normalized_mark_density_probability ν hI hM
  have hm : Measurable (fun p : ℝ × S => p.1+F p.2) := measurable_fst.add (hF.comp measurable_snd)
  have he : (((stableLogIntensity b).prod ν).map (fun p : ℝ × S => p.1+F p.2)) =
      stableLogIntensity b := by
    change Measure.map (Prod.fst ∘ logMarkShift F) ((stableLogIntensity b).prod ν) = _
    rw [← Measure.map_map measurable_fst (logMarkShift_measurable hF),stableLogIntensity_mark_shift ν hb hF,
      Measure.map_fst_prod,measure_univ,one_smul]
  rw [poissonRandomMeasureLaw_map _ hm]
  simp only [he]

lemma poissonWeightedTotal_normalized_log_memLp {S : Type*} [MeasurableSpace S] [Nonempty S]
    (ν : Measure S) [IsProbabilityMeasure ν] {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1)
    {F : S → ℝ} (hF : Measurable F)
    (hI : Integrable (fun x => Real.exp (b*F x)) ν)
    (hM : (∫ x, Real.exp (b*F x) ∂ν) = 1) :
    MemLp (fun η => Real.log (poissonWeightedTotal F η)) 2
      (poissonRandomMeasureLaw ((stableLogIntensity b).prod ν)) := by
  have hpres : MeasurePreserving (Measure.map (fun p : ℝ × S => p.1+F p.2))
      (poissonRandomMeasureLaw ((stableLogIntensity b).prod ν))
      (poissonRandomMeasureLaw (stableLogIntensity b)) :=
    ⟨Measure.measurable_map _ (measurable_fst.add (hF.comp measurable_snd)),
      stablePoisson_normalized_mark_projection ν hb0.le hF hI hM⟩
  simpa only [Function.comp_def,poissonWeightedTotal_eq hF] using
    (stablePoissonTotal_log_memLp_two hb0 hb1).comp_measurePreserving hpres

lemma poissonWeightedTotal_normalized_pos {S : Type*} [MeasurableSpace S] [Nonempty S]
    (ν : Measure S) [IsProbabilityMeasure ν] {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1)
    {F : S → ℝ} (hF : Measurable F)
    (hI : Integrable (fun x => Real.exp (b*F x)) ν)
    (hM : (∫ x, Real.exp (b*F x) ∂ν) = 1) :
    ∀ᵐ η ∂poissonRandomMeasureLaw ((stableLogIntensity b).prod ν), 0 < poissonWeightedTotal F η := by
  have he := stablePoisson_normalized_mark_projection ν hb0.le hF hI hM
  have hh := stablePoissonTotal_pos hb0 hb1
  rw [← he] at hh
  have hh' := (ae_map_iff (Measure.measurable_map _
    (measurable_fst.add (hF.comp measurable_snd))).aemeasurable
      (measurableSet_lt measurable_const stablePoissonTotal_measurable)).mp hh
  simpa only [poissonWeightedTotal_eq hF, Pi.add_def, Function.comp_def] using hh'

lemma poissonWeightedTotal_normalized_log_mean {S : Type*} [MeasurableSpace S] [Nonempty S]
    (ν : Measure S) [IsProbabilityMeasure ν] {b : ℝ} (hb : 0 ≤ b)
    {F : S → ℝ} (hF : Measurable F)
    (hI : Integrable (fun x => Real.exp (b*F x)) ν)
    (hM : (∫ x, Real.exp (b*F x) ∂ν) = 1) :
    (∫ η, Real.log (poissonWeightedTotal F η)
      ∂poissonRandomMeasureLaw ((stableLogIntensity b).prod ν)) =
    ∫ η, Real.log (stablePoissonTotal η) ∂poissonRandomMeasureLaw (stableLogIntensity b) := by
  rw [← stablePoisson_normalized_mark_projection ν hb hF hI hM]
  have h := integral_map (μ := poissonRandomMeasureLaw ((stableLogIntensity b).prod ν))
    (Measure.measurable_map _ (measurable_fst.add (hF.comp measurable_snd))).aemeasurable
    stablePoissonTotal_measurable.log.aestronglyMeasurable
  simp only [Pi.add_def, Function.comp_def] at h
  rw [h]
  simp only [poissonWeightedTotal_eq hF]

lemma stablePoisson_log_recursion {S : Type*} [MeasurableSpace S] [Nonempty S]
    (ν : Measure S) [IsProbabilityMeasure ν] {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1)
    {X : S → ℝ} (hX : Measurable X)
    (hI : Integrable (fun x => Real.exp (b*X x)) ν) :
    (∫ η, Real.log (poissonWeightedTotal X η / poissonWeightedTotal (fun _ => 0) η)
      ∂poissonRandomMeasureLaw ((stableLogIntensity b).prod ν)) =
    Real.log (∫ x, Real.exp (b*X x) ∂ν)/b := by
  let c := Real.log (∫ x, Real.exp (b*X x) ∂ν)/b
  let F := fun x => X x-c
  have hF : Measurable F := hX.sub_const c
  have hMpos := integral_exp_pos hI
  have hfac (x : S) : Real.exp (b*F x) = Real.exp (-b*c)*Real.exp (b*X x) := by
    dsimp [F]
    rw [← Real.exp_add]
    congr 1
    ring
  have hFI : Integrable (fun x => Real.exp (b*F x)) ν := by
    simp_rw [hfac]
    exact hI.const_mul _
  have hFM : (∫ x, Real.exp (b*F x) ∂ν) = 1 := by
    simp_rw [hfac]
    rw [integral_const_mul,show -b*c = -Real.log (∫ x, Real.exp (b*X x) ∂ν) by dsimp [c]; field_simp,
      Real.exp_neg,Real.exp_log hMpos,inv_mul_cancel₀ hMpos.ne']
  have h0I : Integrable (fun _ : S => Real.exp (b*0)) ν := by simp
  have h0M : (∫ _ : S, Real.exp (b*0) ∂ν) = 1 := by simp
  have hlogF := poissonWeightedTotal_normalized_log_memLp ν hb0 hb1 hF hFI hFM
  have hlog0 := poissonWeightedTotal_normalized_log_memLp ν hb0 hb1 measurable_const h0I h0M
  have hEq : (fun η => Real.log (poissonWeightedTotal X η / poissonWeightedTotal (fun _ => 0) η)) =ᵐ[
      poissonRandomMeasureLaw ((stableLogIntensity b).prod ν)]
      (fun η => c+Real.log (poissonWeightedTotal F η)-Real.log (poissonWeightedTotal (fun _ => 0) η)) := by
    filter_upwards [poissonWeightedTotal_normalized_pos ν hb0 hb1 hF hFI hFM,
      poissonWeightedTotal_normalized_pos ν hb0 hb1 measurable_const h0I h0M] with η hηF hη0
    have hs : poissonWeightedTotal X η = Real.exp c*poissonWeightedTotal F η := by
      convert poissonWeightedTotal_add_const hF c η using 1
      congr 1
      funext x
      dsimp [F]
      ring
    rw [Real.log_div (by rw [hs]; positivity) hη0.ne',hs,
      Real.log_mul (Real.exp_pos _).ne' hηF.ne',Real.log_exp]
  have he := integral_sub ((integrable_const c).add (hlogF.integrable (by norm_num)))
    (hlog0.integrable (by norm_num))
  have he' := integral_add (integrable_const c) (hlogF.integrable (by norm_num))
  simp only [Pi.add_apply] at he he'
  rw [integral_congr_ae hEq,he,he',
    poissonWeightedTotal_normalized_log_mean ν hb0.le hF hFI hFM,
    poissonWeightedTotal_normalized_log_mean ν hb0.le measurable_const h0I h0M]
  simp [c]

end SphericalPerceptron

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace

namespace SphericalPerceptron

lemma charFunDual_standardGaussian (L : StrongDual ℝ ℝ) :
    charFunDual (gaussianReal 0 1) L = Complex.exp (-(L 1 : ℂ)^2/2) := by
  have he : (L : ℝ → ℝ) = fun x => L 1*x := by
    funext x
    have h := L.map_smul x (1 : ℝ)
    simpa only [smul_eq_mul,mul_one,mul_comm x,one_mul] using h
  have hm : (∫ x : ℝ, L 1*x ∂gaussianReal 0 1) = 0 := by
    rw [integral_const_mul]
    simp
  have hv : variance (fun x : ℝ => L 1*x) (gaussianReal 0 1) = (L 1)^2 := by
    change variance (fun x : ℝ => L 1*id x) (gaussianReal 0 1) = _
    rw [variance_const_mul]
    simp [variance_id_gaussianReal]
  rw [IsGaussian.charFunDual_eq, integral_complex_ofReal, he, hm, hv]
  congr 1
  push_cast only [Complex.ofReal_zero,Complex.ofReal_pow]
  ring_nf

end SphericalPerceptron
end
end
end

end OAI
