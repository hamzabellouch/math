import OAI.NumberTheory.PrimePackets.LeafSupport

namespace OAI

/-! # Measurability of support membership in a second-countable fiber -/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open scoped Topology

namespace PrimeDegreePackets

lemma measurableSet_kernel_support_secondCountable
    {S T : Type*} [MeasurableSpace S] [TopologicalSpace T] [MeasurableSpace T]
    [OpensMeasurableSpace T] [SecondCountableTopology T] (κ : Kernel S T) :
    MeasurableSet {z : S × T | z.2 ∈ (κ z.1).support} := by
  have hmem (s : S) (t : T) : t ∈ (κ s).support ↔
      ∀ U : countableBasis T, t ∈ U.val → 0 < κ s U.val := by
    simpa only [Subtype.forall, and_imp] using
      ((isBasis_countableBasis T).nhds_hasBasis (a := t)).mem_measureSupport (μ := κ s)
  have heq : {z : S × T | z.2 ∈ (κ z.1).support} =
      ⋂ U : countableBasis T, {z | z.2 ∈ U.val → 0 < κ z.1 U.val} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, hmem]
  rw [heq]
  apply MeasurableSet.iInter
  intro U
  have hU : MeasurableSet U.val := (isOpen_of_mem_countableBasis U.prop).measurableSet
  exact (measurable_snd hU).imp
    (measurableSet_lt measurable_const ((κ.measurable_coe hU).comp measurable_fst))

end PrimeDegreePackets

end

end OAI
