import OAI.NumberTheory.Jacobsthal.Paths.FiniteVisitMass

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.PairedCostGrouping NumberTheoryLean.FinitePathGeometry
open NumberTheoryLean.TransitionKernels NumberTheoryLean.CycleOccupation

lemma witnessContinuation_first_lintegral (z : FirstPairWitness) {F : EvenState → ℝ≥0∞}
    (hF : Measurable F) : (∫⁻ w, F w.1 ∂witnessContinuation z)=F z.1 := by
  rw [witnessContinuation,Kernel.map_apply _ continueWitnessUpdate_measurable,
    lintegral_map (f := fun w : SourceCycleWitness => F w.1) (g := continueWitnessUpdate) (hF.comp measurable_fst) continueWitnessUpdate_measurable,
    Kernel.lintegral_id_prod (f := fun x : FirstPairWitness × (ℕ × OddCost) => F (continueWitnessUpdate x).1)
      ((hF.comp measurable_fst).comp continueWitnessUpdate_measurable)]
  change (∫⁻ _w, F z.1 ∂durationHitOrReturn z.2)=F z.1
  simp

lemma sourceCycleWitness_first_lintegral (z : OddCost) {F : CostState → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ w, F (sourceReturnSignature z w).2.1 ∂sourceCycleWitnessKernel z)=
      ∫⁻ y, F y ∂costKernel (embedOdd z) := by
  have hG : Measurable (fun t : EvenState => F (Sum.inl t,z.2+cost t.1)) :=
    hF.comp (measurable_inl.prodMk (measurable_const.add (cost_measurable.comp measurable_subtype_coe)))
  rw [sourceCycleWitnessKernel,Kernel.lintegral_comp _ _ _
    (g := fun w : SourceCycleWitness => F (sourceReturnSignature z w).2.1)
    (hF.comp ((measurable_fst.comp measurable_snd).comp (sourceReturnSignature_measurable z)))]
  change (∫⁻ y : FirstPairWitness, ∫⁻ w, (fun t : EvenState => F (Sum.inl t,z.2+cost t.1)) w.1
    ∂witnessContinuation y ∂pairWitnessKernel z)=_
  simp_rw [witnessContinuation_first_lintegral _ hG]
  rw [pairWitness_lintegral z (F := fun y : FirstPairWitness => F (Sum.inl y.1,z.2+cost y.1.1))
    (hG.comp measurable_fst)]
  simp only [lintegral_const,measure_univ,mul_one]
  exact (costKernel_odd_lintegral z.1 z.2 hF).symm

theorem sourceCycleWitness_first_arrival (z : OddCost) :
    (sourceCycleWitnessKernel z).map (fun w => (sourceReturnSignature z w).2.1)=costKernel (embedOdd z) := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map (g := fun w : SourceCycleWitness => (sourceReturnSignature z w).2.1) hF ((measurable_fst.comp measurable_snd).comp (sourceReturnSignature_measurable z))]
  exact sourceCycleWitness_first_lintegral z hF

theorem rawReturn_first_arrival (a : ℕ) (h : RawHistory a) (z : OddCost)
    (hz : rawLast a h=embedOdd z) :
    (rawReturnTraceKernel a h).map (fun r => (rawReturnSignature a r).2.1)=costKernel (rawLast a h) := by
  have he := congrArg (fun μ : Measure ReturnSignature => μ.map (fun s => s.2.1))
    (rawReturnTrace_signature a h z hz)
  rw [Measure.map_map (g := fun s : ReturnSignature => s.2.1)
    (measurable_fst.comp measurable_snd) (rawReturnSignature_measurable a),
    Measure.map_map (g := fun s : ReturnSignature => s.2.1)
    (measurable_fst.comp measurable_snd) (sourceReturnSignature_measurable z)] at he
  rw [hz]
  exact he.trans (sourceCycleWitness_first_arrival z)

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
