import OAI.Probability.IsingPerceptron.RetainedDisplacement

namespace OAI

/-! Observable pushforwards from a conditional replica law. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace InvariantIsing

lemma map_compProd_snd {Ω X Y : Type} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure Ω) [SFinite P] (K : Kernel Ω X) [IsSFiniteKernel K]
    {F : X → Y} (hF : Measurable F) :
    (P ⊗ₘ K).map (fun p => F p.2) = (K ∘ₘ P).map F := by
  change (P ⊗ₘ K).map (F ∘ Prod.snd) = _
  rw [← Measure.map_map hF measurable_snd]
  change Measure.map F (P ⊗ₘ K).snd = _
  rw [Measure.snd_compProd]

end InvariantIsing

end

end OAI
