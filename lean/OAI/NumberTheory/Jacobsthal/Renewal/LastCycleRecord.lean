import OAI.NumberTheory.Jacobsthal.Probability.RawEvenMarkedHit

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.PairedCostGrouping NumberTheoryLean.FinitePathGeometry
open NumberTheoryLean.TransitionKernels

noncomputable def lastCycleRecord : (w : List Bool) → (b : Bool) →
    CycleWordSignature (w++[b]).length → CycleInputSignature
  | [], _b, s => s.1
  | _c::w, b, s => lastCycleRecord w b s.2

lemma lastCycleRecord_measurable (w : List Bool) : ∀ b, Measurable (lastCycleRecord w b) := by
  induction w with
  | nil => intro b; exact measurable_fst
  | cons c w ih => intro b; exact (ih b).comp measurable_snd

lemma lastCycleRecord_cost (w : List Bool) (b : Bool) (s : CycleWordSignature (w++[b]).length) :
    (lastCycleRecord w b s).1=lookaheadInputCost w b s := by
  induction w with
  | nil => rfl
  | cons c w ih => exact ih s.2

noncomputable def sourceRecordKernel (b : Bool) : Kernel OddCost CycleInputSignature :=
  (Kernel.id ×ₖ sourceBranchWitnessKernel b).map (fun p => sourceCycleInputSignature p.1 p.2)

instance sourceRecordKernel_isFiniteKernel (b : Bool) : IsFiniteKernel (sourceRecordKernel b) := by
  unfold sourceRecordKernel
  infer_instance

lemma sourceRecordKernel_apply (b : Bool) (z : OddCost) :
    sourceRecordKernel b z=(sourceBranchWitnessKernel b z).map (sourceCycleInputSignature z) := by
  ext S hS
  rw [sourceRecordKernel,Kernel.map_apply' _ sourceCycleInputSignature_measurable _ hS,
    Kernel.id_prod_apply' _ _ (sourceCycleInputSignature_measurable hS),
    Measure.map_apply (f := sourceCycleInputSignature z) (sourceCycleInputSignature_measurable.comp measurable_prodMk_left) hS]
  rfl

lemma sourceRecordKernel_lintegral (b : Bool) (z : OddCost) {F : CycleInputSignature → ℝ≥0∞}
    (hF : Measurable F) : (∫⁻ s, F s ∂sourceRecordKernel b z) =
      ∫⁻ y, F (sourceCycleInputSignature z y) ∂sourceBranchWitnessKernel b z := by
  rw [sourceRecordKernel_apply,lintegral_map (g := sourceCycleInputSignature z) hF
    (sourceCycleInputSignature_measurable.comp measurable_prodMk_left)]

lemma sourceLastRecord_lintegral (w : List Bool) (b : Bool)
    {F : CycleInputSignature → ℝ≥0∞} (hF : Measurable F) : ∀ z,
    (∫⁻ s, F (lastCycleRecord w b s) ∂sourceMarkedWordKernel (w++[b]) z) =
      ∫⁻ y, ∫⁻ t, F t ∂sourceRecordKernel b y ∂branchWordKernel w z := by
  have hG : Measurable (fun y : OddCost => ∫⁻ t, F t ∂sourceRecordKernel b y) := hF.lintegral_kernel
  induction w with
  | nil =>
    intro z
    change (∫⁻ s : CycleWordSignature [b].length, F (lastCycleRecord [] b s) ∂sourceMarkedWordKernel [b] z) = _
    rw [sourceMarkedWord_cons_lintegral b [] z
      (F := fun s => F (lastCycleRecord [] b s)) (hF.comp (lastCycleRecord_measurable [] b))]
    change (∫⁻ y : SourceCycleWitness, ∫⁻ _s, F (sourceCycleInputSignature z y)
      ∂Measure.dirac (embedOdd y.2.2) ∂sourceBranchWitnessKernel b z) =
      ∫⁻ y, ∫⁻ t, F t ∂sourceRecordKernel b y ∂Measure.dirac z
    simp only [lintegral_const,measure_univ,mul_one]
    rw [lintegral_dirac' z hG,sourceRecordKernel_lintegral b z hF]
  | cons c w ih =>
    intro z
    change (∫⁻ s : CycleWordSignature (c::(w++[b])).length,
      F (lastCycleRecord (c::w) b s) ∂sourceMarkedWordKernel (c::(w++[b])) z) = _
    rw [sourceMarkedWord_cons_lintegral c (w++[b]) z
      (F := fun s => F (lastCycleRecord (c::w) b s)) (hF.comp (lastCycleRecord_measurable (c::w) b))]
    change (∫⁻ y : SourceCycleWitness, ∫⁻ s, F (lastCycleRecord w b s)
      ∂sourceMarkedWordKernel (w++[b]) y.2.2 ∂sourceBranchWitnessKernel c z) = _
    simp_rw [ih]
    have hJ : Measurable (fun y : OddCost => ∫⁻ t, ∫⁻ u, F u ∂sourceRecordKernel b t ∂branchWordKernel w y) :=
      hG.lintegral_kernel
    rw [← lintegral_map (g := fun y : SourceCycleWitness => y.2.2) hJ (measurable_snd.comp measurable_snd),
      sourceBranchWitness_endpoint,branchWordKernel,Kernel.lintegral_comp _ _ _ hG]

theorem sourceLastRecord_law (w : List Bool) (b : Bool) (z : OddCost) :
    (sourceMarkedWordKernel (w++[b]) z).map (lastCycleRecord w b)=
      (sourceRecordKernel b ∘ₖ branchWordKernel w) z := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF (lastCycleRecord_measurable w b),Kernel.lintegral_comp _ _ _ hF]
  exact sourceLastRecord_lintegral w b hF z

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
