import Mathlib
import OAI.Probability.Perceptron.Cascade.StablePoissonTotalLogMemLpTwo

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
@[fun_prop] lemma measurable_measure_restrict {S : Type*} [MeasurableSpace S]
    {E : Set S} (hE : MeasurableSet E) : Measurable (fun η : Measure S => η.restrict E) := by
  apply Measure.measurable_of_measurable_coe
  intro t ht
  simp only [Measure.restrict_apply ht]
  exact Measure.measurable_coe (ht.inter hE)

lemma poissonRandomMeasureLaw_mecke_finite {S : Type*} [MeasurableSpace S] [Nonempty S]
    (κ : Measure S) [IsFiniteMeasure κ]
    {H : Measure S × S → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ η, ∫⁻ x, H (η,x) ∂η ∂poissonRandomMeasureLaw κ) =
      ∫⁻ x, ∫⁻ η, H (Measure.dirac x + η,x) ∂poissonRandomMeasureLaw κ ∂κ := by
  rw [poissonRandomMeasureLaw_of_finite κ,finitePoissonLaw_mecke _ _ hH]
  calc
    _ = ∫⁻ x, ∫⁻ η, H (Measure.dirac x+η,x)
        ∂finitePoissonLaw (κ univ).toNNReal (finiteIntensityMarks κ)
        ∂((κ univ).toNNReal : ℝ≥0∞) • finiteIntensityMarks κ := by
      rw [lintegral_smul_measure]; rfl
    _ = _ := by rw [finiteIntensityMarks_smul κ]

lemma poissonRandomMeasureLaw_mecke_restrict {S : Type*} [MeasurableSpace S] [Nonempty S]
    (κ : Measure S) [SFinite κ] {E : Set S} (hE : MeasurableSet E) (hκ : κ E < ⊤)
    {H : Measure S × S → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ η, ∫⁻ x in E, H (η,x) ∂η ∂poissonRandomMeasureLaw κ) =
      ∫⁻ x in E, ∫⁻ η, H (Measure.dirac x + η,x) ∂poissonRandomMeasureLaw κ ∂κ := by
  let ν := κ.restrict E
  let ζ := κ.restrict Eᶜ
  let P := poissonRandomMeasureLaw ν
  let Q := poissonRandomMeasureLaw ζ
  have : IsFiniteMeasure ν := ⟨by simpa [ν] using hκ⟩
  have hsum : ν+ζ = κ := Measure.restrict_add_restrict_compl hE
  have hadd : Measurable (fun p : Measure S × Measure S => p.1+p.2) := by fun_prop
  have hPQ : (P.prod Q).map (fun p => p.1+p.2) = poissonRandomMeasureLaw κ := by
    dsimp [P,Q]
    rw [poissonRandomMeasureLaw_superposition]
    simp only [hsum]
  have hm : AEMeasurable (fun η : Measure S => ∫⁻ x in E, H (η,x) ∂η)
      (poissonRandomMeasureLaw κ) :=
    aemeasurable_randomMeasure_lintegral_of_finite (measurable_measure_restrict hE)
      (poissonRandomMeasureLaw_ae_restrict_finite κ hE hκ) hH
  have hPnull : ∀ᵐ η ∂P, η Eᶜ = 0 := by
    apply poissonRandomMeasureLaw_ae_null ν hE.compl
    simp [ν,Measure.restrict_apply,hE.compl]
  have hQnull : ∀ᵐ η ∂Q, η E = 0 := by
    apply poissonRandomMeasureLaw_ae_null ζ hE
    simp [ζ,Measure.restrict_apply,hE]
  have hPQnull : ∀ᵐ p : Measure S × Measure S ∂P.prod Q,
      p.1 Eᶜ = 0 ∧ p.2 E = 0 := by
    apply (Measure.ae_prod_iff_ae_ae
      ((measurableSet_eq_fun ((Measure.measurable_coe hE.compl).comp measurable_fst) measurable_const).inter
        (measurableSet_eq_fun ((Measure.measurable_coe hE).comp measurable_snd) measurable_const))).mpr
    filter_upwards [hPnull] with η hη
    filter_upwards [hQnull] with ξ hξ
    exact ⟨hη,hξ⟩
  have hrestrict (η ξ : Measure S) (hη : η Eᶜ = 0) (hξ : ξ E = 0) :
      (η+ξ).restrict E = η := by
    rw [Measure.restrict_add,Measure.restrict_eq_zero.mpr hξ,add_zero]
    have hh := Measure.restrict_add_restrict_compl (μ := η) hE
    rwa [Measure.restrict_eq_zero.mpr hη,add_zero] at hh
  have haefin : ∀ᵐ p : Measure S × Measure S ∂P.prod Q, p.1 univ < ⊤ := by
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_lt ((Measure.measurable_coe MeasurableSet.univ).comp measurable_fst) measurable_const)).mpr
    filter_upwards [poissonRandomMeasureLaw_ae_restrict_finite ν MeasurableSet.univ
      (measure_lt_top ν univ)] with η hη
    exact ae_of_all _ fun _ => by simpa using hη
  have hmeas : AEMeasurable (fun p : Measure S × Measure S =>
      ∫⁻ x, H (p.1+p.2,x) ∂p.1) (P.prod Q) :=
    aemeasurable_randomMeasure_lintegral_of_finite measurable_fst haefin
      (hH.comp (by fun_prop : Measurable (fun p : (Measure S × Measure S) × S => (p.1.1+p.1.2,p.2))))
  calc
    _ = ∫⁻ p : Measure S × Measure S, ∫⁻ x in E, H (p.1+p.2,x) ∂(p.1+p.2) ∂P.prod Q := by
      rw [← hPQ] at hm ⊢
      exact lintegral_map' hm hadd.aemeasurable
    _ = ∫⁻ p : Measure S × Measure S, ∫⁻ x, H (p.1+p.2,x) ∂p.1 ∂P.prod Q := by
      apply lintegral_congr_ae
      filter_upwards [hPQnull] with p hp
      rw [hrestrict p.1 p.2 hp.1 hp.2]
    _ = ∫⁻ ξ, ∫⁻ η, ∫⁻ x, H (η+ξ,x) ∂η ∂P ∂Q := lintegral_prod_symm _ hmeas
    _ = ∫⁻ ξ, ∫⁻ x, ∫⁻ η, H (Measure.dirac x+η+ξ,x) ∂P ∂ν ∂Q := by
      apply lintegral_congr
      intro ξ
      exact poissonRandomMeasureLaw_mecke_finite ν (hH.comp
        (by fun_prop : Measurable (fun p : Measure S × S => (p.1+ξ,p.2))))
    _ = ∫⁻ x, ∫⁻ ξ, ∫⁻ η, H (Measure.dirac x+η+ξ,x) ∂P ∂Q ∂ν := by
      apply lintegral_lintegral_swap
      exact (hH.comp (by fun_prop : Measurable (fun p : (Measure S × S) × Measure S =>
        (Measure.dirac p.1.2+p.2+p.1.1,p.1.2)))).lintegral_prod_right'.aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro x
      rw [← lintegral_prod_symm (μ := P) (ν := Q)
        (fun p : Measure S × Measure S => H (Measure.dirac x+p.1+p.2,x)) (hH.comp (by fun_prop : Measurable
        (fun p : Measure S × Measure S => (Measure.dirac x+p.1+p.2,x)))).aemeasurable]
      rw [← hPQ,lintegral_map (f := fun η : Measure S => H (Measure.dirac x+η,x)) (hH.comp (by fun_prop : Measurable
        (fun η : Measure S => (Measure.dirac x+η,x)))) hadd]
      apply lintegral_congr
      intro p
      rw [add_assoc]

lemma poissonRandomMeasureLaw_mecke {S : Type*} [MeasurableSpace S] [Nonempty S]
    (κ : Measure S) [SigmaFinite κ] {H : Measure S × S → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ η, ∫⁻ x, H (η,x) ∂η ∂poissonRandomMeasureLaw κ) =
      ∫⁻ x, ∫⁻ η, H (Measure.dirac x + η,x) ∂poissonRandomMeasureLaw κ ∂κ := by
  have hset (η : Measure S) : (∫⁻ x, H (η,x) ∂η) =
      ⨆ n : ℕ, ∫⁻ x in spanningSets κ n, H (η,x) ∂η := by
    rw [← setLIntegral_iUnion_of_directed _ (monotone_spanningSets κ).directed_le,
      iUnion_spanningSets,Measure.restrict_univ]
  simp_rw [hset]
  rw [lintegral_iSup']
  · simp_rw [poissonRandomMeasureLaw_mecke_restrict κ (measurableSet_spanningSets κ _)
      (measure_spanningSets_lt_top κ _) hH]
    rw [← setLIntegral_iUnion_of_directed _ (monotone_spanningSets κ).directed_le,
      iUnion_spanningSets,Measure.restrict_univ]
  · intro n
    exact aemeasurable_randomMeasure_lintegral_of_finite (measurable_measure_restrict (measurableSet_spanningSets κ n))
      (poissonRandomMeasureLaw_ae_restrict_finite κ (measurableSet_spanningSets κ n)
        (measure_spanningSets_lt_top κ n)) hH
  · exact ae_of_all _ fun η n m hnm => lintegral_mono_set (monotone_spanningSets κ hnm)

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

end SphericalPerceptronFreeEnergy

end

end OAI
