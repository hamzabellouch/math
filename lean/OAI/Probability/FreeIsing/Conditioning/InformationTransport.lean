import OAI.Probability.FreeIsing.Conditioning.ComponentInformation
import OAI.Probability.FreeIsing.Conditioning.Pullback

namespace OAI

noncomputable section
open MeasureTheory
open scoped NNReal

namespace Problem367

section Transport

variable {Ω Ξ : Type*} [mΩ : MeasurableSpace Ω] [mΞ : MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]

theorem posterior_information_comp_measurePreserving
    (e : Ω → Ξ) (he : MeasurePreserving e μ ν)
    (m : MeasurableSpace Ξ) (hm : m ≤ mΞ) {f : Ξ → ℝ} (hf : Integrable f ν) :
    (∫ ω, (condExp (m.comap e) μ (f ∘ e) ω) ^ 2 ∂μ) =
      ∫ ξ, (condExp m ν f ξ) ^ 2 ∂ν := by
  let : MeasurableSpace Ξ := mΞ
  calc
    _ = ∫ ω, (condExp m ν f (e ω)) ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [condExp_comp_measurePreserving μ ν e he m hm hf] with ω hω
      exact congrArg (fun z : ℝ => z ^ 2) hω
    _ = _ := by
      have hp : StronglyMeasurable (condExp m ν f) := stronglyMeasurable_condExp.mono hm
      exact he.hasLaw.integral_comp (f := fun ξ => (condExp m ν f ξ) ^ 2)
        (hp.pow 2).aestronglyMeasurable

theorem posterior_information_le_of_measurePreserving
    (e : Ω → Ξ) (he : MeasurePreserving e μ ν)
    (m : MeasurableSpace Ξ) (hm : m ≤ mΞ)
    (M : MeasurableSpace Ω) (hM : M ≤ mΩ) (hobs : m.comap e ≤ M)
    {f : Ξ → ℝ} (hf : MemLp f 2 ν) :
    (∫ ξ, (condExp m ν f ξ) ^ 2 ∂ν) ≤
      ∫ ω, (condExp M μ (f ∘ e) ω) ^ 2 ∂μ := by
  let : MeasurableSpace Ω := mΩ
  let : MeasurableSpace Ξ := mΞ
  rw [← posterior_information_comp_measurePreserving μ ν e he m hm
    (hf.integrable (by norm_num))]
  exact posterior_information_mono hobs hM (hf.comp_measurePreserving he)

end Transport

theorem HasFreeIsingLaw.component_critical_information_lower_transport
    {d : ℕ} {theta : ℝ} {mu : Measure (TreeVertex d → IsingSpin)}
    (hmu : HasFreeIsingLaw theta mu) (hlo : -1 ≤ theta) (hhi : theta ≤ 1)
    (c : Fin d) (hcritical : ((d - 1 : ℕ) : ℝ) * theta ^ 2 = 1)
    {t : ℝ≥0} (ht : 0 < t)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (e : Ω → (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ))
    (he : MeasurePreserving e P (mu.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)))
    (M : MeasurableSpace Ω) (hM : M ≤ mΩ)
    (hobs : (PlantedInformation.observationSigma (componentIndexVertex (c := c)) t).comap e ≤ M) :
    min (Real.sqrt (t : ℝ)) 1 / 5 ≤
      ∫ ω, (condExp M P (fun η => spinSign ((e η).1 ⟨[c], List.IsChain.singleton c⟩)) ω) ^ 2 ∂P := by
  let : MeasurableSpace Ω := mΩ
  let := hmu.isProbabilityMeasure
  apply (hmu.component_critical_information_lower hlo hhi c hcritical ht).trans
  apply posterior_information_le_of_measurePreserving P
    (mu.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)) e he
    (PlantedInformation.observationSigma (componentIndexVertex (c := c)) t)
    (PlantedInformation.observationSigma_le _ _) M hM hobs
  exact (PlantedInformation.spinSign_memLp mu ⟨[c], List.IsChain.singleton c⟩).comp_measurePreserving
    measurePreserving_fst

end Problem367

end

end OAI
