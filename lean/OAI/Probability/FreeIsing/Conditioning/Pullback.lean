import Mathlib

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem setIntegral_comp_measurePreserving
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') (e : Ω → Ω')
    (he : MeasurePreserving e μ ν) {f : Ω' → ℝ}
    (hf : AEStronglyMeasurable f ν) {B : Set Ω'} (hB : MeasurableSet B) :
    (∫ ω in e ⁻¹' B, f (e ω) ∂μ) = ∫ ω' in B, f ω' ∂ν := by
  have hres := he.restrict_preimage hB
  have hfm : AEStronglyMeasurable f (Measure.map e (μ.restrict (e ⁻¹' B))) := by
    rw [hres.map_eq]
    exact hf.restrict
  calc
    _ = ∫ ω', f ω' ∂Measure.map e (μ.restrict (e ⁻¹' B)) :=
      (integral_map hres.measurable.aemeasurable hfm).symm
    _ = _ := by rw [hres.map_eq]

theorem condExp_comp_measurePreserving
    {Ω Ω' : Type*} [mΩ : MeasurableSpace Ω] [mΩ' : MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (e : Ω → Ω') (he : MeasurePreserving e μ ν)
    (m : MeasurableSpace Ω') (hm : m ≤ mΩ')
    {f : Ω' → ℝ} (hf : Integrable f ν) :
    μ[f ∘ e | m.comap e] =ᵐ[μ] (ν[f | m]) ∘ e := by
  let : MeasurableSpace Ω' := mΩ'
  have hsource : m.comap e ≤ mΩ :=
    (MeasurableSpace.comap_mono hm).trans he.measurable.comap_le
  have hcompint : Integrable ((ν[f | m]) ∘ e) μ :=
    he.integrable_comp_of_integrable integrable_condExp
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hsource
    (he.integrable_comp_of_integrable hf)
    (fun _ _ _ => hcompint.integrableOn)
  · intro A hA _
    obtain ⟨B, hB, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hA
    simp only [Function.comp_apply]
    rw [setIntegral_comp_measurePreserving μ ν e he (f := ν[f | m])
        integrable_condExp.aestronglyMeasurable (hm B hB),
      setIntegral_comp_measurePreserving μ ν e he hf.aestronglyMeasurable (hm B hB),
      setIntegral_condExp hm hf hB]
  · exact (stronglyMeasurable_condExp.comp_measurable
      (Measurable.of_comap_le le_rfl)).aestronglyMeasurable

theorem condIndepFun_comp_measurePreserving
    {Ω Ω' C D : Type*} [mΩ : MeasurableSpace Ω] [mΩ' : MeasurableSpace Ω']
    [MeasurableSpace C] [MeasurableSpace D]
    [StandardBorelSpace Ω] [StandardBorelSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (e : Ω → Ω') (he : MeasurePreserving e μ ν)
    (m : MeasurableSpace Ω') (hm : m ≤ mΩ')
    {f : Ω' → C} {g : Ω' → D}
    (hf : @Measurable Ω' C mΩ' _ f) (hg : @Measurable Ω' D mΩ' _ g)
    (hfg : CondIndepFun m hm f g ν) :
    CondIndepFun (m.comap e)
      ((MeasurableSpace.comap_mono hm).trans (@Measurable.comap_le Ω Ω' mΩ mΩ' e
        (@MeasurePreserving.measurable Ω Ω' mΩ mΩ' e μ ν he)))
      (f ∘ e) (g ∘ e) μ := by
  let : MeasurableSpace Ω' := mΩ'
  classical
  rw [condIndepFun_iff_condExp_inter_preimage_eq_mul
    (hf.comp he.measurable) (hg.comp he.measurable)]
  intro U V hU hV
  have hE := hU.preimage hf
  have hH := hV.preimage hg
  have hCE := condExp_comp_measurePreserving μ ν e he m hm
    ((integrable_const (1 : ℝ)).indicator hE)
  have hCH := condExp_comp_measurePreserving μ ν e he m hm
    ((integrable_const (1 : ℝ)).indicator hH)
  have hCEH := condExp_comp_measurePreserving μ ν e he m hm
    ((integrable_const (1 : ℝ)).indicator (hE.inter hH))
  have hmul := he.quasiMeasurePreserving.ae_eq_comp
    ((condIndepFun_iff_condExp_inter_preimage_eq_mul hf hg).mp hfg U V hU hV)
  filter_upwards [hCE, hCH, hCEH, hmul] with ω hωE hωH hωEH hωmul
  exact hωEH.trans (hωmul.trans (congrArg₂ (· * ·) hωE.symm hωH.symm))

theorem ae_eq_iff_comp_measurePreserving
    {Ω Ω' C : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace C] [MeasurableEq C]
    (μ : Measure Ω) (ν : Measure Ω') (e : Ω → Ω')
    (he : MeasurePreserving e μ ν) {f g : Ω' → C}
    (hf : Measurable f) (hg : Measurable g) :
    f =ᵐ[ν] g ↔ f ∘ e =ᵐ[μ] g ∘ e := by
  rw [← he.map_eq]
  exact ae_map_iff he.measurable.aemeasurable (measurableSet_eq_fun hf hg)

end Problem367

end

end OAI
