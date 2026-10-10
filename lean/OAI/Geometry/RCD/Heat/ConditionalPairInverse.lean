import OAI.Geometry.RCD.Sobolev.ConditionalSelfPair
import OAI.Geometry.RCD.Heat.DiagonalConditionalKernel

namespace OAI

/-! # A diagonal conditional self-coupling gives a measurable inverse -/

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
noncomputable section
namespace RegularPointCoordinates
variable {A Z : Type*} [MeasurableSpace A] [MeasurableSpace Z]
  [StandardBorelSpace A] [Nonempty A] [MeasurableSpace.CountablyGenerated Z]
  [MeasurableEq Z]

theorem measurable_inverse_of_conditional_diagonal (μ : Measure A) [IsFiniteMeasure μ]
    (f : A → Z) (hf : Measurable f)
    (h : ∀ᵐ z ∂conditionalSelfPair μ f hf, z.1=z.2) :
    ∃ g : Z → A, Measurable g ∧ ∀ᵐ a ∂μ, g (f a)=a := by
  let η := (Kernel.deterministic f hf)†μ
  obtain ⟨g,hg,he⟩ := kernel_dirac_of_diagonal_self_product (μ.map f) η h
  have hη : η ∘ₘ (μ.map f)=μ := by
    simpa only [Measure.deterministic_comp_eq_map] using
      (posterior_comp_self (κ:=Kernel.deterministic f hf) (μ:=μ))
  have hfiber : ∀ᵐ z ∂μ.map f, ∀ᵐ a ∂η z, f a=z := by
    filter_upwards [deterministic_comp_posterior (μ:=μ) hf] with z hz
    have hm : (η z).map f=Measure.dirac z := by
      simpa only [Kernel.deterministic_comp_eq_map,Kernel.map_apply _ hf,Kernel.id_apply] using hz
    apply ae_of_ae_map (μ:=η z) (p:=fun a => a=z) hf.aemeasurable
    rw [hm]
    simp
  refine ⟨g,hg,?_⟩
  rw [←hη]
  apply Measure.ae_comp_of_ae_ae (measurableSet_eq_fun (hg.comp hf) measurable_id)
  filter_upwards [he,hfiber] with z hz hfz
  have hfg : f (g z)=z := by simpa only [hz,ae_dirac_eq,Filter.eventually_pure] using hfz
  simpa only [hz,ae_dirac_eq,Filter.eventually_pure,Function.comp_apply,id_eq] using congrArg g hfg

theorem injective_on_full_set_of_conditional_diagonal (μ : Measure A) [IsFiniteMeasure μ]
    (f : A → Z) (hf : Measurable f)
    (h : ∀ᵐ z ∂conditionalSelfPair μ f hf, z.1=z.2) :
    ∃ S : Set A, MeasurableSet S ∧ (∀ᵐ a ∂μ, a ∈ S) ∧ InjOn f S := by
  obtain ⟨g,hg,hinv⟩ := measurable_inverse_of_conditional_diagonal μ f hf h
  refine ⟨{a | g (f a)=a},measurableSet_eq_fun (hg.comp hf) measurable_id,hinv,?_⟩
  intro a ha b hb hab
  exact ha.symm.trans ((congrArg g hab).trans hb)

end RegularPointCoordinates

end

end OAI
