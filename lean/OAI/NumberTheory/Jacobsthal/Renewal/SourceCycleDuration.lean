import OAI.NumberTheory.Jacobsthal.Probability.MovingMarkedWindow

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ProbabilityTheory ENNReal
open NumberTheoryLean.TransitionKernels NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.CostReturnLaw NumberTheoryLean.InitialRegeneration
open NumberTheoryLean.MarkedCycleLaw

noncomputable def durationHitOrReturn : Kernel OddCost (ℕ × OddCost) := by
  classical
  exact Kernel.piecewise returnSet_measurable
    (Kernel.deterministic (fun z => (0,z)) (measurable_const.prodMk measurable_id)) markedReturnLaw

instance durationHitOrReturn_isMarkovKernel : IsMarkovKernel durationHitOrReturn := by
  unfold durationHitOrReturn
  infer_instance

lemma durationHitOrReturn_forget (z : OddCost) :
    (durationHitOrReturn z).map Prod.snd = hitOrReturn z := by
  classical
  rw [durationHitOrReturn,Kernel.piecewise_apply,hitOrReturn,Kernel.piecewise_apply]
  split_ifs
  · rw [Kernel.deterministic_apply,Measure.map_dirac' measurable_snd]
    rfl
  · exact markedReturnLaw_forget z

abbrev FirstPairWitness := EvenState × OddCost
abbrev SourceCycleWitness := EvenState × (ℕ × OddCost)

noncomputable def pairWitnessUpdate (x : OddCost × (EvenState × OddState)) : FirstPairWitness :=
  (x.2.1,pairUpdate x)

lemma pairWitnessUpdate_measurable : Measurable pairWitnessUpdate :=
  (measurable_fst.comp measurable_snd).prodMk pairUpdate_measurable

noncomputable def pairWitnessKernel : Kernel OddCost FirstPairWitness :=
  (Kernel.id ×ₖ pairedDraws.prodMkRight ℝ).map pairWitnessUpdate

instance pairWitnessKernel_isMarkovKernel : IsMarkovKernel pairWitnessKernel :=
  Kernel.IsMarkovKernel.map _ pairWitnessUpdate_measurable

noncomputable def firstPairProjection (z : FirstPairWitness) : MarkedOddCost := (sourceMark z.1,z.2)

lemma firstPairProjection_measurable : Measurable firstPairProjection :=
  (sourceMark_measurable.comp measurable_fst).prodMk measurable_snd

lemma pairWitness_projection (z : OddCost) :
    (pairWitnessKernel z).map firstPairProjection = markedPairKernel z := by
  rw [pairWitnessKernel,Kernel.map_apply _ pairWitnessUpdate_measurable,
    Measure.map_map firstPairProjection_measurable pairWitnessUpdate_measurable,
    markedPairKernel,Kernel.map_apply _ markedPairUpdate_measurable]
  rfl

noncomputable def continueWitnessUpdate (x : FirstPairWitness × (ℕ × OddCost)) : SourceCycleWitness :=
  (x.1.1,(2+x.2.1,x.2.2))

lemma continueWitnessUpdate_measurable : Measurable continueWitnessUpdate :=
  (measurable_fst.comp measurable_fst).prodMk
    ((measurable_const.add (measurable_fst.comp measurable_snd)).prodMk (measurable_snd.comp measurable_snd))

noncomputable def witnessContinuation : Kernel FirstPairWitness SourceCycleWitness :=
  (Kernel.id ×ₖ durationHitOrReturn.prodMkLeft EvenState).map continueWitnessUpdate

instance witnessContinuation_isMarkovKernel : IsMarkovKernel witnessContinuation :=
  Kernel.IsMarkovKernel.map _ continueWitnessUpdate_measurable

lemma witnessContinuation_apply (z : FirstPairWitness) {B : Set SourceCycleWitness} (hB : MeasurableSet B) :
    witnessContinuation z B = durationHitOrReturn z.2 {d | (z.1,(2+d.1,d.2)) ∈ B} := by
  rw [witnessContinuation,Kernel.map_apply' _ continueWitnessUpdate_measurable _ hB,
    Kernel.prod_apply' _ _ _ (continueWitnessUpdate_measurable hB),Kernel.id_apply,lintegral_dirac']
  · rfl
  · exact measurable_measure_prodMk_left (continueWitnessUpdate_measurable hB)

noncomputable def sourceWitnessProjection (x : SourceCycleWitness) : MarkedOddCost :=
  (sourceMark x.1,x.2.2)

lemma sourceWitnessProjection_measurable : Measurable sourceWitnessProjection :=
  (sourceMark_measurable.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd)

lemma witnessContinuation_projection (z : FirstPairWitness) :
    (witnessContinuation z).map sourceWitnessProjection = markContinuation (firstPairProjection z) := by
  ext B hB
  rw [Measure.map_apply sourceWitnessProjection_measurable hB,
    witnessContinuation_apply _ (sourceWitnessProjection_measurable hB),markContinuation_apply _ hB]
  have he := congrArg (fun μ : Measure OddCost => μ {y | (sourceMark z.1,y) ∈ B})
    (durationHitOrReturn_forget z.2)
  have hm : MeasurableSet {y : OddCost | (sourceMark z.1,y) ∈ B} :=
    (measurable_const.prodMk measurable_id) hB
  rw [Measure.map_apply measurable_snd hm] at he
  exact he

noncomputable def sourceCycleWitnessKernel : Kernel OddCost SourceCycleWitness :=
  witnessContinuation ∘ₖ pairWitnessKernel

instance sourceCycleWitnessKernel_isMarkovKernel : IsMarkovKernel sourceCycleWitnessKernel := by
  unfold sourceCycleWitnessKernel
  infer_instance

lemma sourceCycleWitness_projection (z : OddCost) :
    (sourceCycleWitnessKernel z).map sourceWitnessProjection = completedMarkedKernel z := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF sourceWitnessProjection_measurable,sourceCycleWitnessKernel,
    Kernel.lintegral_comp _ _ _ (g := fun x : SourceCycleWitness => F (sourceWitnessProjection x))
      (hF.comp sourceWitnessProjection_measurable)]
  have he (x : FirstPairWitness) : (∫⁻ y, F (sourceWitnessProjection y) ∂witnessContinuation x) =
      ∫⁻ y, F y ∂markContinuation (firstPairProjection x) := by
    rw [← witnessContinuation_projection x,lintegral_map hF sourceWitnessProjection_measurable]
  simp_rw [he]
  have hJ : Measurable (fun z : MarkedOddCost => ∫⁻ y, F y ∂markContinuation z) := hF.lintegral_kernel
  rw [← lintegral_map (g := firstPairProjection) hJ firstPairProjection_measurable,
    pairWitness_projection,completedMarkedKernel,Kernel.lintegral_comp _ _ _ hF]

lemma sourceCycleWitness_duration_ge_two (z : OddCost) :
    ∀ᵐ x ∂sourceCycleWitnessKernel z, 2 ≤ x.2.1 := by
  rw [sourceCycleWitnessKernel]
  apply Kernel.ae_comp_of_ae_ae (measurableSet_le measurable_const (measurable_fst.comp measurable_snd))
  apply Eventually.of_forall
  intro y
  rw [witnessContinuation,Kernel.map_apply _ continueWitnessUpdate_measurable]
  apply (ae_map_iff continueWitnessUpdate_measurable.aemeasurable
    (measurableSet_le measurable_const (measurable_fst.comp measurable_snd))).mpr
  exact Eventually.of_forall (fun x => by change 2 ≤ 2+x.2.1; omega)

lemma sourceWitness_mark_iff (x : SourceCycleWitness) :
    (sourceWitnessProjection x).1 = true ↔ (209/100:ℝ) ≤ x.1.1 ∧ x.1.1 ≤ 213/100 := by
  simp [sourceWitnessProjection,sourceMark]

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ProbabilityTheory ENNReal
open NumberTheoryLean.PairedCostProcess NumberTheoryLean.CostReturnLaw
open NumberTheoryLean.InitialRegeneration NumberTheoryLean.MarkedCycleLaw

noncomputable def addPairDuration (z : ℕ × OddCost) : ℕ × OddCost := (2+z.1,z.2)

lemma addPairDuration_measurable : Measurable addPairDuration :=
  (measurable_const.add measurable_fst).prodMk measurable_snd

lemma durationHit_comp_captured : durationHitOrReturn ∘ₖ costCaptured =
    costCaptured.map (fun z => (0,z)) := by
  classical
  let D : Kernel OddCost (ℕ × OddCost) := Kernel.deterministic (fun z => ((0:ℕ),z))
    (measurable_const.prodMk measurable_id)
  have hk : durationHitOrReturn ∘ₖ costCaptured = D ∘ₖ costCaptured := by
    ext z B hB
    rw [Kernel.comp_apply' _ _ _ hB,Kernel.comp_apply' _ _ _ hB]
    apply lintegral_congr_ae
    have hae : ∀ᵐ y ∂costCaptured z, y ∈ returnSet := by
      rw [costCaptured,Kernel.restrict_apply]
      exact ae_restrict_mem returnSet_measurable
    filter_upwards [hae] with y hy
    rw [durationHitOrReturn,Kernel.piecewise_apply,ite_eq_left hy]
  rw [hk]
  exact Kernel.deterministic_comp_eq_map _ _

lemma durationHit_comp_killed : durationHitOrReturn ∘ₖ costKilled = markedReturnLaw ∘ₖ costKilled := by
  classical
  ext z B hB
  rw [Kernel.comp_apply' _ _ _ hB,Kernel.comp_apply' _ _ _ hB]
  apply lintegral_congr_ae
  have hae : ∀ᵐ y ∂costKilled z, y ∉ returnSet := by
    rw [costKilled,Kernel.restrict_apply]
    exact ae_restrict_mem returnSet_measurable.compl
  filter_upwards [hae] with y hy
  rw [durationHitOrReturn,Kernel.piecewise_apply,ite_eq_right hy]

lemma firstMarkedReturn_succ (n : ℕ) :
    firstMarkedReturn (n+1) = ((firstMarkedReturn n) ∘ₖ costKilled).map addPairDuration := by
  unfold firstMarkedReturn
  rw [← Kernel.map_comp,← Kernel.map_comp_right _ (markReturn_measurable n) addPairDuration_measurable,
    firstReturn_succ_comp]
  congr 1
  funext z
  simp only [Function.comp_def,addPairDuration,markReturn,Prod.mk.injEq,and_true]
  omega

lemma markedReturnLaw_first_step_duration :
    markedReturnLaw = firstMarkedReturn 0+(markedReturnLaw ∘ₖ costKilled).map addPairDuration := by
  ext z B hB
  rw [markedReturnLaw,Kernel.sum_apply' _ _ hB,_root_.add_apply,Measure.add_apply,
    Kernel.map_apply' _ addPairDuration_measurable _ hB,Kernel.comp_sum_left,
    Kernel.sum_apply' _ _ (addPairDuration_measurable hB),tsum_eq_zero_add' ENNReal.summable]
  congr 1
  apply tsum_congr
  intro n
  rw [firstMarkedReturn_succ,Kernel.map_apply' _ addPairDuration_measurable _ hB]

lemma duration_forced_first_pair :
    (durationHitOrReturn ∘ₖ pairedCostKernel).map addPairDuration = markedReturnLaw := by
  rw [← costCaptured_add_costKilled,Kernel.comp_add_right,durationHit_comp_captured,durationHit_comp_killed]
  conv_rhs => rw [markedReturnLaw_first_step_duration]
  ext z B hB
  rw [Kernel.map_apply' _ addPairDuration_measurable _ hB,_root_.add_apply,Measure.add_apply,
    _root_.add_apply,Measure.add_apply,
    Kernel.map_apply' _ addPairDuration_measurable _ hB]
  congr 1
  rw [Kernel.map_apply' _ (f := fun z : OddCost => ((0:ℕ),z)) (measurable_const.prodMk measurable_id) _ (addPairDuration_measurable hB),
    firstMarkedReturn,Kernel.map_apply' _ (markReturn_measurable 0) _ hB]
  change costCaptured z ((fun y => (0,y)) ⁻¹' addPairDuration ⁻¹' B) =
    firstReturn 0 z (markReturn 0 ⁻¹' B)
  have hz : firstReturn 0 = costCaptured := Kernel.comp_id _
  rw [hz]
  rfl

lemma pairWitness_forget (z : OddCost) : (pairWitnessKernel z).map Prod.snd = pairedCostKernel z := by
  rw [pairWitnessKernel,Kernel.map_apply _ pairWitnessUpdate_measurable,
    Measure.map_map measurable_snd pairWitnessUpdate_measurable,
    pairedCostKernel,Kernel.map_apply _ pairUpdate_measurable]
  rfl

lemma witnessContinuation_duration (z : FirstPairWitness) :
    (witnessContinuation z).map Prod.snd = (durationHitOrReturn z.2).map addPairDuration := by
  ext B hB
  rw [Measure.map_apply measurable_snd hB,witnessContinuation_apply _ (measurable_snd hB),
    Measure.map_apply addPairDuration_measurable hB]
  rfl

theorem sourceCycleWitness_duration_law (z : OddCost) :
    (sourceCycleWitnessKernel z).map Prod.snd = markedReturnLaw z := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF measurable_snd,sourceCycleWitnessKernel,
    Kernel.lintegral_comp _ _ _ (g := fun x : SourceCycleWitness => F x.2) (hF.comp measurable_snd)]
  have he (x : FirstPairWitness) : (∫⁻ y, F y.2 ∂witnessContinuation x) =
      ∫⁻ y, F (addPairDuration y) ∂durationHitOrReturn x.2 := by
    rw [← lintegral_map (g := Prod.snd) hF measurable_snd,witnessContinuation_duration,
      lintegral_map hF addPairDuration_measurable]
  simp_rw [he]
  have hJ : Measurable (fun z : OddCost => ∫⁻ y, F (addPairDuration y) ∂durationHitOrReturn z) :=
    (hF.comp addPairDuration_measurable).lintegral_kernel
  rw [← lintegral_map (g := Prod.snd) hJ measurable_snd,pairWitness_forget,
    ← Kernel.lintegral_comp _ _ _ (g := fun y : ℕ × OddCost => F (addPairDuration y))
      (hF.comp addPairDuration_measurable),
    ← lintegral_map (g := addPairDuration) hF addPairDuration_measurable]
  have hd := congrArg (fun K : Kernel OddCost (ℕ × OddCost) => K z) duration_forced_first_pair
  rw [Kernel.map_apply _ addPairDuration_measurable] at hd
  rw [hd]

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
