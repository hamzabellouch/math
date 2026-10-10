import OAI.InformationTheory.Entanglement.ConditionalUpdate

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Function
open scoped MeasureTheory ProbabilityTheory unitInterval
namespace SecretKey
variable {Ω S N Y : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
  [MeasurableSpace N] [StandardBorelSpace N] [Nonempty N]
  [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma independent_noise_condDistrib (H : Ω → S) (U : Ω → N)
    (hH : Measurable H) (hU : Measurable U) (hind : IndepFun H U μ) :
    condDistrib U H μ =ᵐ[μ.map H] Kernel.const S (μ.map U) := by
  apply condDistrib_ae_eq_of_measure_eq_compProd_of_measurable hH hU
  rw [Measure.compProd_const]
  exact hind.map_prod_eq_prod_map_map hH.aemeasurable hU.aemeasurable

omit [StandardBorelSpace Y] [Nonempty Y] in
theorem sampled_conditional_event (H : Ω → S) (U : Ω → N)
    (hH : Measurable H) (hU : Measurable U) (hind : IndepFun H U μ)
    (f : S → N → Y) (hf : Measurable (uncurry f))
    (κ : Kernel S Y) [IsMarkovKernel κ]
    (hmap : ∀ s, (μ.map U).map (f s) = κ s)
    (E : Set Y) (hE : MeasurableSet E) :
    (μ⟦(fun ω => f (H ω) (U ω)) ⁻¹' E | (inferInstance : MeasurableSpace S).comap H⟧)
      =ᵐ[μ] fun ω => (κ (H ω)).real E := by
  let g : S × N → ℝ := fun v => E.indicator (fun _ => (1 : ℝ)) (f v.1 v.2)
  have hg : StronglyMeasurable g :=
    (measurable_const.indicator hE |>.comp hf).stronglyMeasurable
  have hgi : Integrable (fun ω => g (H ω,U ω)) μ := by
    change Integrable (((fun ω => f (H ω) (U ω)) ⁻¹' E).indicator (fun _ => (1 : ℝ))) μ
    exact (integrable_const (1 : ℝ)).indicator (hE.preimage (hf.comp (hH.prodMk hU)))
  have hc := condExp_prod_ae_eq_integral_condDistrib hH hU.aemeasurable hg hgi
  have hd := independent_noise_condDistrib H U hH hU hind
  have hd' := ae_of_ae_map hH.aemeasurable hd
  have hfun : ((fun ω => f (H ω) (U ω)) ⁻¹' E).indicator (fun _ => (1 : ℝ)) =
      (fun ω => g (H ω,U ω)) := by
    ext ω
    by_cases hx : f (H ω) (U ω) ∈ E <;> simp [g, hx]
  change condExp _ μ _ =ᵐ[μ] _
  rw [hfun]
  filter_upwards [hc,hd'] with ω he hdω
  rw [he,hdω]
  change (∫ u, E.indicator (fun _ => (1 : ℝ)) (f (H ω) u) ∂μ.map U) = _
  rw [← integral_map (by fun_prop) (by fun_prop), hmap]
  simp [measureReal_def, integral_indicator hE]

theorem exists_uniform_conditional_sampler (κ : Kernel S Y) [IsMarkovKernel κ] :
    ∃ f : S → I → Y, Measurable (uncurry f) ∧
      (∀ s, volume.map (f s)=κ s) ∧
      ∀ (H : Ω → S) (U : Ω → I), Measurable H → Measurable U → IndepFun H U μ →
        μ.map U=volume → ∀ E, MeasurableSet E →
          (μ⟦(fun ω => f (H ω) (U ω)) ⁻¹' E | (inferInstance : MeasurableSpace S).comap H⟧)
            =ᵐ[μ] fun ω => (κ (H ω)).real E := by
  obtain ⟨f,hf,hmap⟩ := κ.exists_measurable_map_eq_unitInterval
  refine ⟨f,hf,hmap,?_⟩
  intro H U hH hU hind hdist E hE
  apply sampled_conditional_event H U hH hU hind f hf κ _ E hE
  simpa only [hdist] using hmap

end SecretKey

end

end OAI
