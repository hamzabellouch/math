import Mathlib.Probability.Kernel.Posterior

namespace OAI

/-! # The independent conditional self-coupling over a measurable observable -/

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
noncomputable section
namespace RegularPointCoordinates
variable {A Z : Type*} [MeasurableSpace A] [MeasurableSpace Z]
  [StandardBorelSpace A] [Nonempty A] [MeasurableSpace.CountablyGenerated Z]
  [MeasurableEq Z]

def conditionalSelfPair (μ : Measure A) [IsFiniteMeasure μ] (f : A → Z) (hf : Measurable f) :
    Measure (A×A) :=
  let η := (Kernel.deterministic f hf)†μ
  (η ×ₖ η) ∘ₘ (μ.map f)

omit [MeasurableSpace.CountablyGenerated Z] [MeasurableEq Z] in
theorem conditionalSelfPair_marginals (μ : Measure A) [IsFiniteMeasure μ]
    (f : A → Z) (hf : Measurable f) :
    (conditionalSelfPair μ f hf).map Prod.fst=μ ∧
      (conditionalSelfPair μ f hf).map Prod.snd=μ := by
  let η := (Kernel.deterministic f hf)†μ
  have hη : η ∘ₘ (μ.map f)=μ := by
    simpa only [Measure.deterministic_comp_eq_map] using
      (posterior_comp_self (κ:=Kernel.deterministic f hf) (μ:=μ))
  constructor
  · rw [conditionalSelfPair,Measure.map_comp _ _ measurable_fst]
    rw [←Kernel.fst_eq,Kernel.fst_prod]
    exact hη
  · rw [conditionalSelfPair,Measure.map_comp _ _ measurable_snd]
    rw [←Kernel.snd_eq,Kernel.snd_prod]
    exact hη

instance conditionalSelfPair_finite (μ : Measure A) [IsFiniteMeasure μ]
    (f : A → Z) (hf : Measurable f) : IsFiniteMeasure (conditionalSelfPair μ f hf) := by
  unfold conditionalSelfPair
  infer_instance

theorem conditionalSelfPair_common (μ : Measure A) [IsFiniteMeasure μ]
    (f : A → Z) (hf : Measurable f) :
    ∀ᵐ z ∂conditionalSelfPair μ f hf, f z.1=f z.2 := by
  let η := (Kernel.deterministic f hf)†μ
  have hη : ∀ᵐ z ∂μ.map f, (η z).map f=Measure.dirac z := by
    filter_upwards [deterministic_comp_posterior (μ:=μ) hf] with z hz
    simpa only [Kernel.deterministic_comp_eq_map,Kernel.map_apply _ hf,Kernel.id_apply] using hz
  change ∀ᵐ z ∂((η ×ₖ η) ∘ₘ (μ.map f)), f z.1=f z.2
  apply Measure.ae_comp_of_ae_ae (measurableSet_eq_fun (hf.comp measurable_fst) (hf.comp measurable_snd))
  filter_upwards [hη] with z hz
  have hpoint : ∀ᵐ a ∂η z, f a=z := by
    apply ae_of_ae_map (μ:=η z) (p:=fun a => a=z) hf.aemeasurable
    rw [hz]
    simp
  rw [Kernel.prod_apply]
  change ∀ᵐ p ∂(η z).prod (η z), f p.1=f p.2
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun (hf.comp measurable_fst) (hf.comp measurable_snd))).mpr
  filter_upwards [hpoint] with a ha
  exact hpoint.mono fun b hb => ha.trans hb.symm

end RegularPointCoordinates

end

end OAI
