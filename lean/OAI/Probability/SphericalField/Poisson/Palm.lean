import Mathlib
import OAI.Probability.SphericalField.Poisson.Superposition

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron
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

end SphericalPerceptron
end
end

end OAI
