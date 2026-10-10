import Mathlib.MeasureTheory.Constructions.Polish.Basic

namespace OAI

/-! Transfer the standard Borel property through a measurable embedding,
using a compatible Polish topology that makes its image closed. -/
open Set Function MeasureTheory Topology
noncomputable section
namespace CircleDomainRigidity

lemma standardBorel_of_measurableEmbedding
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B] [StandardBorelSpace B]
    {f : A → B} (hf : MeasurableEmbedding f) : StandardBorelSpace A := by
  obtain ⟨t, htB, htP, hclosed, _⟩ := hf.measurableSet_range.isClopenable'
  let : TopologicalSpace B := t
  let : BorelSpace B := htB
  let : PolishSpace B := htP
  let ta : TopologicalSpace A := TopologicalSpace.induced f t
  let : TopologicalSpace A := ta
  have htop : IsClosedEmbedding f := ⟨⟨⟨rfl⟩, hf.injective⟩, hclosed⟩
  refine ⟨⟨ta, ?_, htop.polishSpace⟩⟩
  constructor
  change (inferInstance : MeasurableSpace A) = @borel A ta
  rw [borel_comap, ← BorelSpace.measurable_eq, hf.comap_eq]

end CircleDomainRigidity

end

end OAI
