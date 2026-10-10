import Mathlib.Probability.Kernel.Condexp
import Mathlib.Tactic

namespace OAI

open MeasureTheory ProbabilityTheory

namespace Invariant233.CrossingAvoidance

variable {Ω β : Type*}

theorem ae_ae_condExpKernel_of_ae (m' : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω}
    [StandardBorelSpace Ω] (hm' : m' ≤ mΩ) (μ : Measure Ω) [IsFiniteMeasure μ]
    {P : Ω → Prop} (hP : ∀ᵐ ω ∂μ, P ω) :
    ∀ᵐ x ∂μ, ∀ᵐ ω ∂condExpKernel μ m' x, P ω := by
  apply ae_of_ae_trim hm'
  apply Measure.ae_ae_of_ae_comp
  rwa [condExpKernel_comp_trim hm']

theorem condExpKernel_ae_eq_of_measurable (m' : MeasurableSpace Ω)
    {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    [mβ : MeasurableSpace β] [MeasurableEq β]
    (hm' : m' ≤ mΩ) (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : Ω → β) (hf : Measurable[m'] f) :
    ∀ᵐ x ∂μ, ∀ᵐ ω ∂condExpKernel μ m' x, f ω = f x := by
  let : MeasurableSpace (Ω × Ω) := m'.prod mΩ
  have hf1 : @Measurable (Ω × Ω) β (m'.prod mΩ) mβ (fun z => f z.1) :=
    hf.comp (@measurable_fst Ω Ω m' mΩ)
  have hf2 : @Measurable (Ω × Ω) β (m'.prod mΩ) mβ (fun z => f z.2) :=
    (hf.mono hm' le_rfl).comp (@measurable_snd Ω Ω m' mΩ)
  have hdiag : @Measurable Ω (Ω × Ω) mΩ (m'.prod mΩ) (fun x => (x, x)) :=
    (measurable_id'' hm').prodMk measurable_id
  have hprod : ∀ᵐ z ∂(μ.trim hm') ⊗ₘ condExpKernel μ m', f z.2 = f z.1 := by
    rw [compProd_trim_condExpKernel hm']
    exact (ae_map_iff hdiag.aemeasurable (measurableSet_eq_fun hf2 hf1)).mpr
      (Filter.Eventually.of_forall (fun _ => rfl))
  exact ae_of_ae_trim hm' (Measure.ae_ae_of_ae_compProd hprod)

end Invariant233.CrossingAvoidance

end OAI
