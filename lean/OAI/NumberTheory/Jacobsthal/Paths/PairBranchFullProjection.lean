import OAI.NumberTheory.Jacobsthal.Renewal.RegenerationInputPotential

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Classical
open NumberTheoryLean.PairedCostProcess NumberTheoryLean.InitialRegeneration

noncomputable def pairBranchKernel (b : Bool) : Kernel OddCost OddCost :=
  (markedPairKernel.restrict (measurable_fst (measurableSet_singleton b))).map Prod.snd

instance pairBranchKernel_isFiniteKernel (b : Bool) : IsFiniteKernel (pairBranchKernel b) := by
  unfold pairBranchKernel
  infer_instance

lemma markedKernel_branch_lintegral (K : Kernel OddCost MarkedOddCost) (b : Bool) (z : OddCost)
    {F : OddCost → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ y, F y ∂((K.restrict (measurable_fst (measurableSet_singleton b))).map Prod.snd) z)=
      ∫⁻ y, (if y.1=b then F y.2 else 0) ∂K z := by
  rw [Kernel.map_apply _ measurable_snd,Kernel.restrict_apply,lintegral_map hF measurable_snd,
    ← lintegral_indicator (measurable_fst (measurableSet_singleton b))]
  apply lintegral_congr
  intro y
  simp only [Set.indicator_apply,mem_preimage,mem_singleton_iff]

lemma markContinuation_measure (z : MarkedOddCost) :
    markContinuation z=(hitOrReturn z.2).map (Prod.mk z.1) := by
  ext S hS
  rw [markContinuation_apply _ hS,Measure.map_apply measurable_prodMk_left hS]
  rfl

theorem cycleBranch_completion (b : Bool) : cycleBranchKernel b=hitOrReturn ∘ₖ pairBranchKernel b := by
  ext z : 1
  apply Measure.ext_of_lintegral
  intro F hF
  let G : MarkedOddCost → ℝ≥0∞ := fun y => if y.1=b then F y.2 else 0
  have hG : Measurable G := Measurable.ite (measurable_fst (measurableSet_singleton b))
    (hF.comp measurable_snd) measurable_const
  have hJ : Measurable (fun y : OddCost => ∫⁻ t, F t ∂hitOrReturn y) := hF.lintegral_kernel
  rw [cycleBranchKernel,markedKernel_branch_lintegral _ b z hF]
  change (∫⁻ y, G y ∂completedMarkedKernel z)=_
  rw [completedMarkedKernel,Kernel.lintegral_comp _ _ _ hG,Kernel.lintegral_comp _ _ _ hF,
    pairBranchKernel,markedKernel_branch_lintegral _ b z hJ]
  apply lintegral_congr
  intro y
  rw [markContinuation_measure,lintegral_map hG measurable_prodMk_left]
  by_cases hy : y.1=b <;> simp [G,hy]

lemma pairBranch_sum : pairBranchKernel true+pairBranchKernel false=NumberTheoryLean.PairedCostProcess.pairedCostKernel := by
  ext z : 1
  rw [_root_.add_apply]
  unfold pairBranchKernel
  rw [Kernel.map_apply _ measurable_snd,Kernel.map_apply _ measurable_snd,Kernel.restrict_apply,Kernel.restrict_apply]
  change ((markedPairKernel z).restrict {y | y.1=true}).map Prod.snd+
    ((markedPairKernel z).restrict {y | y.1=false}).map Prod.snd=_
  rw [false_mark_set]
  change ((markedPairKernel z).restrict sourceMarkSet).map Prod.snd+
    ((markedPairKernel z).restrict sourceMarkSetᶜ).map Prod.snd=_
  rw [← Measure.map_add _ _ measurable_snd,Measure.restrict_add_restrict_compl sourceMarkSet_measurable,markedPair_forget]

lemma nextMarkWeight_pair_mass (z : OddCost) : nextMarkWeight z=pairBranchKernel true z univ := by
  rw [nextMarkWeight,cycleBranch_completion,Kernel.comp_apply' _ _ _ MeasurableSet.univ]
  simp

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Classical
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.PairedCostGrouping

lemma pairBranch_full_lintegral (b : Bool) (z : OddCost) {F : CostState → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ y, F (embedOdd y) ∂pairBranchKernel b z)=
      ∫⁻ s, (if firstArrivalMark s=b then ∫⁻ t, F t ∂costKernel s else 0) ∂costKernel (embedOdd z) := by
  let G : MarkedOddCost → ℝ≥0∞ := fun y => if y.1=b then F (embedOdd y.2) else 0
  have hG : Measurable G := Measurable.ite (measurable_fst (measurableSet_singleton b))
    (hF.comp (embedOdd_measurable.comp measurable_snd)) measurable_const
  let J : CostState × CostState → ℝ≥0∞ := fun y => if firstArrivalMark y.1=b then F y.2 else 0
  have hJ : Measurable J := Measurable.ite ((firstArrivalMark_measurable.comp measurable_fst) (measurableSet_singleton b))
    (hF.comp measurable_snd) measurable_const
  rw [pairBranchKernel,markedKernel_branch_lintegral _ b z (F := fun y => F (embedOdd y)) (hF.comp embedOdd_measurable)]
  change (∫⁻ y, G y ∂markedPairKernel z)=_
  rw [← pairWitness_projection z,lintegral_map hG firstPairProjection_measurable]
  calc
    _ = ∫⁻ y, J y ∂fullPairTraceKernel (embedOdd z) := by
      rw [← pairWitness_joint_full_trace z,lintegral_map hJ (pairTraceOfWitness_measurable z)]
      rfl
    _ = _ := by
      rw [fullPairTraceKernel,Kernel.lintegral_compProd _ _ _ hJ]
      apply lintegral_congr
      intro s
      by_cases hs : firstArrivalMark s=b <;> simp [J,hs]

lemma pairBranch_full_projection (b : Bool) (z : OddCost) :
    (pairBranchKernel b z).map embedOdd=
      (costKernel ∘ₖ costKernel.restrict (firstArrivalMark_measurable (measurableSet_singleton b))) (embedOdd z) := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF embedOdd_measurable,pairBranch_full_lintegral b z hF,
    Kernel.lintegral_comp _ _ _ hF,Kernel.restrict_apply,
    ← lintegral_indicator (firstArrivalMark_measurable (measurableSet_singleton b))]
  apply lintegral_congr
  intro s
  simp only [Set.indicator_apply,mem_preimage,mem_singleton_iff]

lemma false_arrival_set : {s : CostState | firstArrivalMark s=false}=markedArrivalᶜ := by
  ext s
  cases he : firstArrivalMark s <;> simp [markedArrival,he]

lemma pairBranch_marked_first_mass (z : OddCost) :
    pairBranchKernel true z univ=(costKernel (embedOdd z)) markedArrival := by
  have he := congrArg (fun μ : Measure CostState => μ univ) (pairBranch_full_projection true z)
  rw [Measure.map_apply embedOdd_measurable MeasurableSet.univ,preimage_univ,
    Kernel.comp_apply' _ _ _ MeasurableSet.univ] at he
  simp only [measure_univ,lintegral_const,one_mul] at he
  rw [Kernel.restrict_apply' _ _ _ MeasurableSet.univ,univ_inter] at he
  exact he

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
