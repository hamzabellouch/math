import OAI.NumberTheory.Jacobsthal.Estimates.ReturnCompletionAlgebra

namespace OAI

namespace Erdos970


namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.TransitionKernels NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.CostReturnLaw NumberTheoryLean.CycleRegeneration
open NumberTheoryLean.InitialRegeneration NumberTheoryLean.RegenerationTails
open NumberTheoryLean.CycleCostLower NumberTheoryLean.FinitePathGeometry

noncomputable def continueMarkUpdate (x : MarkedOddCost × OddCost) : MarkedOddCost := (x.1.1,x.2)

lemma continueMarkUpdate_measurable : Measurable continueMarkUpdate :=
  (measurable_fst.comp measurable_fst).prodMk measurable_snd

noncomputable def markContinuation : Kernel MarkedOddCost MarkedOddCost :=
  (Kernel.id ×ₖ hitOrReturn.prodMkLeft Bool).map continueMarkUpdate

instance markContinuation_isMarkovKernel : IsMarkovKernel markContinuation :=
  Kernel.IsMarkovKernel.map _ continueMarkUpdate_measurable

lemma markContinuation_apply (z : MarkedOddCost) {B : Set MarkedOddCost} (hB : MeasurableSet B) :
    markContinuation z B = hitOrReturn z.2 {y | (z.1,y) ∈ B} := by
  rw [markContinuation,Kernel.map_apply' _ continueMarkUpdate_measurable _ hB,
    Kernel.prod_apply' _ _ _ (continueMarkUpdate_measurable hB),Kernel.id_apply,lintegral_dirac']
  · rfl
  · exact measurable_measure_prodMk_left (continueMarkUpdate_measurable hB)

lemma markContinuation_forget (z : MarkedOddCost) :
    (markContinuation z).map Prod.snd = hitOrReturn z.2 := by
  ext B hB
  rw [Measure.map_apply measurable_snd hB,markContinuation_apply _ (measurable_snd hB)]
  rfl

noncomputable def completedMarkedKernel : Kernel OddCost MarkedOddCost :=
  markContinuation ∘ₖ markedPairKernel

instance completedMarkedKernel_isMarkovKernel : IsMarkovKernel completedMarkedKernel := by
  unfold completedMarkedKernel
  infer_instance

lemma completedMarked_forget (z : OddCost) :
    (completedMarkedKernel z).map Prod.snd = returnLaw z := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF measurable_snd,completedMarkedKernel,
    Kernel.lintegral_comp _ _ _ (g := fun y : MarkedOddCost => F y.2) (hF.comp measurable_snd)]
  have he (y : MarkedOddCost) : (∫⁻ t, F t.2 ∂markContinuation y) = ∫⁻ t, F t ∂hitOrReturn y.2 := by
    rw [← markContinuation_forget y,lintegral_map hF measurable_snd]
  simp_rw [he]
  have hJ : Measurable (fun y : OddCost => ∫⁻ t, F t ∂hitOrReturn y) := hF.lintegral_kernel
  calc
    _ = ∫⁻ y : OddCost, ∫⁻ t, F t ∂hitOrReturn y ∂pairedCostKernel z := by
      rw [← markedPair_forget z,lintegral_map hJ measurable_snd]
    _ = _ := by rw [← complete_first_pair,Kernel.lintegral_comp _ _ _ hF]

lemma completedMarked_regeneration (s : OddState) (hs : s.1 ≤ 3) (T : ℝ) :
    completedMarkedKernel (s,T) = completedMarkedKernel (regenerationState,T) := by
  ext B hB
  rw [completedMarkedKernel,Kernel.comp_apply' _ _ _ hB,Kernel.comp_apply' _ _ _ hB,
    markedPair_regeneration s hs T]

lemma markContinuation_preserves_mark (z : MarkedOddCost) :
    markContinuation z {y | y.1=true} = if z.1=true then 1 else 0 := by
  have hB : MeasurableSet {y : MarkedOddCost | y.1=true} := measurable_fst (measurableSet_singleton true)
  rw [markContinuation_apply _ hB]
  by_cases hz : z.1=true <;> simp [hz]

lemma completedMarked_mark_eq (z : OddCost) :
    completedMarkedKernel z {y | y.1=true} = markedPairKernel z {y | y.1=true} := by
  let B : Set MarkedOddCost := {y | y.1=true}
  have hB : MeasurableSet B := measurable_fst (measurableSet_singleton true)
  rw [completedMarkedKernel,Kernel.comp_apply' _ _ _ hB]
  calc
    _ = ∫⁻ y, B.indicator (fun _ => (1:ℝ≥0∞)) y ∂markedPairKernel z := by
      apply lintegral_congr
      intro y
      rw [markContinuation_preserves_mark]
      simp [B,Set.indicator_apply]
    _ = ∫⁻ _y in B, (1:ℝ≥0∞) ∂markedPairKernel z := lintegral_indicator hB _
    _ = _ := by simp [B]

lemma completedMarked_mark_mass (s : OddState) (hs : s.1 ≤ 3) (T : ℝ) :
    completedMarkedKernel (s,T) {y | y.1=true} = markProbability := by
  rw [completedMarked_mark_eq,markedPair_mark_mass s hs T]

lemma completedMarked_cost_lower (z : OddCost) :
    ∀ᵐ y ∂completedMarkedKernel z, z.2+cost 3 ≤ y.2.2 := by
  have he := returnLaw_cost_lower z
  rw [← completedMarked_forget z] at he
  exact (ae_map_iff measurable_snd.aemeasurable (measurableSet_le measurable_const measurable_snd)).mp he

lemma markContinuation_translation (z : MarkedOddCost) (a : ℝ) :
    (markContinuation z).map (markedShift a) = markContinuation (markedShift a z) := by
  ext B hB
  rw [Measure.map_apply (markedShift_measurable a) hB,
    markContinuation_apply _ ((markedShift_measurable a) hB),markContinuation_apply _ hB]
  change hitOrReturn z.2 {y | (z.1,shiftCost a y) ∈ B} =
    hitOrReturn (shiftCost a z.2) {y | (z.1,y) ∈ B}
  have hD : MeasurableSet {y : OddCost | (z.1,y) ∈ B} :=
    (measurable_const.prodMk measurable_id) hB
  rw [← hitOrReturn_translation z.2 a,Measure.map_apply (shiftCost_measurable a) hD]
  rfl

lemma completedMarked_translation (s : OddState) (T a : ℝ) :
    (completedMarkedKernel (s,T)).map (markedShift a) = completedMarkedKernel (s,T+a) := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF (markedShift_measurable a),completedMarkedKernel,
    Kernel.lintegral_comp _ _ _ (g := fun y : MarkedOddCost => F (markedShift a y)) (hF.comp (markedShift_measurable a)),Kernel.lintegral_comp _ _ _ hF]
  have he (z : MarkedOddCost) : (∫⁻ y, F (markedShift a y) ∂markContinuation z) =
      ∫⁻ y, F y ∂markContinuation (markedShift a z) := by
    rw [← markContinuation_translation z a,lintegral_map hF (markedShift_measurable a)]
  simp_rw [he]
  have hJ : Measurable (fun z : MarkedOddCost => ∫⁻ y, F y ∂markContinuation z) := hF.lintegral_kernel
  rw [← markedPair_translation s T a,lintegral_map hJ (markedShift_measurable a)]

end Erdos970Dependency.MarkedVisits


end Erdos970

end OAI
