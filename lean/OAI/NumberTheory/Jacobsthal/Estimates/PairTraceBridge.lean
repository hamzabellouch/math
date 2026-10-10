import OAI.NumberTheory.Jacobsthal.Renewal.SourceCycleDuration

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.TransitionKernels NumberTheoryLean.FinitePathGeometry
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.PairedCostGrouping NumberTheoryLean.CycleOccupation

lemma pairWitness_lintegral (z : OddCost) {F : FirstPairWitness → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ y, F y ∂pairWitnessKernel z) =
      ∫⁻ t : EvenState, ∫⁻ u : OddState, F (t,(u,z.2+cost t.1+cost u.1)) ∂evenToOdd t ∂oddToEven z.1 := by
  have hm : Measurable (fun x : EvenState × OddState => pairWitnessUpdate (z,x)) :=
    pairWitnessUpdate_measurable.comp measurable_prodMk_left
  have he : pairWitnessKernel z = (pairedDraws z.1).map (fun x => pairWitnessUpdate (z,x)) :=
    sampling_map_measure pairWitnessUpdate pairWitnessUpdate_measurable z
  rw [he,lintegral_map hF hm,pairedDraws,
    Kernel.lintegral_compProd _ _ _ (f := fun x : EvenState × OddState => F (pairWitnessUpdate (z,x))) (hF.comp hm)]
  rfl

noncomputable def pairTraceOfWitness (z : OddCost) (x : FirstPairWitness) : CostState × CostState :=
  ((Sum.inl x.1,z.2+cost x.1.1),embedOdd x.2)

lemma pairTraceOfWitness_measurable (z : OddCost) : Measurable (pairTraceOfWitness z) :=
  ((measurable_inl.comp measurable_fst).prodMk
    (measurable_const.add (cost_measurable.comp (measurable_subtype_coe.comp measurable_fst)))).prodMk
    (embedOdd_measurable.comp measurable_snd)

noncomputable def fullPairTraceKernel : Kernel CostState (CostState × CostState) :=
  costKernel ⊗ₖ costKernel.prodMkLeft CostState

instance fullPairTraceKernel_isMarkovKernel : IsMarkovKernel fullPairTraceKernel := by
  unfold fullPairTraceKernel
  infer_instance

theorem pairWitness_joint_full_trace (z : OddCost) :
    (pairWitnessKernel z).map (pairTraceOfWitness z) = fullPairTraceKernel (embedOdd z) := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF (pairTraceOfWitness_measurable z),
    pairWitness_lintegral z (F := fun x : FirstPairWitness => F (pairTraceOfWitness z x)) (hF.comp (pairTraceOfWitness_measurable z)),fullPairTraceKernel,
    Kernel.lintegral_compProd _ _ _ hF]
  change (∫⁻ t : EvenState, ∫⁻ u : OddState,
      F ((Sum.inl t,z.2+cost t.1),(Sum.inr u,z.2+cost t.1+cost u.1)) ∂evenToOdd t ∂oddToEven z.1) =
    ∫⁻ x : CostState, ∫⁻ y : CostState, F (x,y) ∂costKernel x ∂costKernel (embedOdd z)
  have hJ : Measurable (fun x : CostState => ∫⁻ y : CostState, F (x,y) ∂costKernel x) :=
    hF.lintegral_kernel_prod_right'
  simp only [embedOdd]
  rw [costKernel_odd_lintegral z.1 z.2 hJ]
  apply lintegral_congr
  intro t
  exact (costKernel_even_lintegral t (z.2+cost t.1)
    (H := fun y : CostState => F ((Sum.inl t,z.2+cost t.1),y))
    (hF.comp measurable_prodMk_left)).symm

theorem pairWitness_joint_event (z : OddCost) {B : Set (CostState × CostState)} (hB : MeasurableSet B) :
    pairWitnessKernel z (pairTraceOfWitness z ⁻¹' B) = fullPairTraceKernel (embedOdd z) B := by
  rw [← Measure.map_apply (pairTraceOfWitness_measurable z) hB,pairWitness_joint_full_trace]

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
