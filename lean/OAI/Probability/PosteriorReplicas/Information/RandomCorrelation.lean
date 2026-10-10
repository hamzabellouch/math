import OAI.Probability.PosteriorReplicas.Information.ParametricKernel

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

lemma klDiv_random_tuple_observation {T Y Z : Type*}
    [MeasurableSpace T] [MeasurableSpace Y] [MeasurableSpace Z]
    [StandardBorelSpace Y] [Nonempty Y] [StandardBorelSpace Z] [Nonempty Z]
    {n : ℕ} (β : Measure T) [IsProbabilityMeasure β]
    (Q : Measure (Fin n → Y)) [IsProbabilityMeasure Q]
    {g : T × Y → Z} (hg : Measurable g) :
    klDiv ((β.prod Q).map (fun z => (z.1,fun i => g (z.1,z.2 i))))
      ((β.prod (marginalProduct Q)).map (fun z => (z.1,fun i => g (z.1,z.2 i)))) =
      ∫⁻ b, totalCorrelation (Q.map (fun u i => g (b,u i))) ∂β := by
  let h : T × (Fin n → Y) → (Fin n → Z) := fun z i => g (z.1,z.2 i)
  have hh : Measurable h := by unfold h; fun_prop
  let κ := parametricMapKernel Q h
  let η := parametricMapKernel (marginalProduct Q) h
  have : IsMarkovKernel κ := parametricMapKernel_markov Q h hh
  have : IsMarkovKernel η := parametricMapKernel_markov (marginalProduct Q) h hh
  rw [← compProd_parametricMapKernel β Q hh,← compProd_parametricMapKernel β (marginalProduct Q) hh]
  change klDiv (β ⊗ₘ κ) (β ⊗ₘ η) = _
  rw [klDiv_compProd_kernel]
  apply lintegral_congr
  intro b
  simp only [κ,η,parametricMapKernel_apply _ hh,h]
  rw [totalCorrelation,marginalProduct_map (ν := Q) (g := fun y => g (b,y)) (by fun_prop)]

end PosteriorReplicas
end

end OAI
