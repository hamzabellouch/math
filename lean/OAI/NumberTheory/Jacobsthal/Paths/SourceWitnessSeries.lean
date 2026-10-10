import OAI.NumberTheory.Jacobsthal.Estimates.JointReturnCylinder

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.TransitionKernels NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.CostReturnLaw NumberTheoryLean.MarkedCycleLaw

noncomputable def tagSourceReturn (n : ℕ) (z : FirstPairWitness) : SourceCycleWitness :=
  (z.1,(2*(n+1),z.2))

lemma tagSourceReturn_measurable (n : ℕ) : Measurable (tagSourceReturn n) :=
  measurable_fst.prodMk (measurable_const.prodMk measurable_snd)

noncomputable def sourceWitnessTerm (n : ℕ) : Kernel OddCost SourceCycleWitness :=
  (sourceReturnTerm n).map (tagSourceReturn n)

instance sourceWitnessTerm_isFiniteKernel (n : ℕ) : IsFiniteKernel (sourceWitnessTerm n) := by
  unfold sourceWitnessTerm
  infer_instance

noncomputable def witnessRemaining : Kernel FirstPairWitness SourceCycleWitness :=
  Kernel.sum (fun n : ℕ => (firstEvenReturnContinuation n).map (tagSourceReturn (n+1)))

instance witnessRemaining_isSFiniteKernel : IsSFiniteKernel witnessRemaining := by
  unfold witnessRemaining
  infer_instance

lemma witnessContinuation_measure (z : FirstPairWitness) :
    witnessContinuation z = (durationHitOrReturn z.2).map (fun d => continueWitnessUpdate (z,d)) := by
  ext B hB
  rw [witnessContinuation_apply _ hB,
    Measure.map_apply (f := fun d : ℕ × OddCost => continueWitnessUpdate (z,d))
      (continueWitnessUpdate_measurable.comp measurable_prodMk_left) hB]
  rfl

lemma witnessContinuation_at_return (z : FirstPairWitness) (hz : z.2 ∈ returnSet) :
    witnessContinuation z = Measure.dirac (tagSourceReturn 0 z) := by
  classical
  rw [witnessContinuation_measure,durationHitOrReturn,Kernel.piecewise_apply,ite_eq_left hz,
    Kernel.deterministic_apply,Measure.map_dirac' (f := fun d : ℕ × OddCost => continueWitnessUpdate (z,d)) (continueWitnessUpdate_measurable.comp measurable_prodMk_left)]
  rfl

lemma witnessContinuation_outside_return (z : FirstPairWitness) (hz : z.2 ∉ returnSet) :
    witnessContinuation z = witnessRemaining z := by
  classical
  rw [witnessContinuation_measure,durationHitOrReturn,Kernel.piecewise_apply,ite_eq_right hz,
    NumberTheoryLean.MarkedCycleLaw.markedReturnLaw,Kernel.sum_apply,
    Measure.map_sum (f := fun d : ℕ × OddCost => continueWitnessUpdate (z,d))
      (continueWitnessUpdate_measurable.comp measurable_prodMk_left).aemeasurable,
    witnessRemaining,Kernel.sum_apply]
  apply congrArg Measure.sum
  funext n
  have he : firstEvenReturnContinuation n z = (firstReturn n z.2).map (fun y => (z.1,y)) := by
    ext B hB
    rw [firstEvenReturnContinuation_apply _ _ hB,
      Measure.map_apply (f := fun y : OddCost => (z.1,y)) (measurable_const.prodMk measurable_id) hB]
    rfl
  rw [firstMarkedReturn,Kernel.map_apply _ (markReturn_measurable n),
    Measure.map_map (g := fun d : ℕ × OddCost => continueWitnessUpdate (z,d)) (f := markReturn n) (continueWitnessUpdate_measurable.comp measurable_prodMk_left) (markReturn_measurable n),
    Kernel.map_apply _ (tagSourceReturn_measurable (n+1)),he,
    Measure.map_map (g := tagSourceReturn (n+1)) (f := fun y : OddCost => (z.1,y)) (tagSourceReturn_measurable (n+1)) (measurable_const.prodMk measurable_id)]
  apply congrArg (fun f => (firstReturn n z.2).map f)
  funext y
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · dsimp [Function.comp_def,continueWitnessUpdate,markReturn,tagSourceReturn]
      omega
    · rfl

lemma firstPairs_partition : capturedFirstPair+killedFirstPair=pairWitnessKernel := by
  ext z : 1
  rw [_root_.add_apply,capturedFirstPair,killedFirstPair,Kernel.restrict_apply,Kernel.restrict_apply]
  simpa only [preimage_compl] using
    Measure.restrict_add_restrict_compl (μ := pairWitnessKernel z) (returnSet_measurable.preimage measurable_snd)

lemma witnessContinuation_comp_captured :
    witnessContinuation ∘ₖ capturedFirstPair = sourceWitnessTerm 0 := by
  let D : Kernel FirstPairWitness SourceCycleWitness := Kernel.deterministic (tagSourceReturn 0) (tagSourceReturn_measurable 0)
  have he : witnessContinuation ∘ₖ capturedFirstPair = D ∘ₖ capturedFirstPair := by
    ext z B hB
    rw [Kernel.comp_apply' _ _ _ hB,Kernel.comp_apply' _ _ _ hB]
    apply lintegral_congr_ae
    have hae : ∀ᵐ y ∂capturedFirstPair z, y.2 ∈ returnSet := by
      rw [capturedFirstPair,Kernel.restrict_apply]
      exact ae_restrict_mem (returnSet_measurable.preimage measurable_snd)
    filter_upwards [hae] with y hy
    rw [witnessContinuation_at_return y hy]
    rfl
  rw [he]
  exact Kernel.deterministic_comp_eq_map _ _

lemma witnessContinuation_comp_killed : witnessContinuation ∘ₖ killedFirstPair =
    Kernel.sum (fun n : ℕ => sourceWitnessTerm (n+1)) := by
  have he : witnessContinuation ∘ₖ killedFirstPair = witnessRemaining ∘ₖ killedFirstPair := by
    ext z B hB
    rw [Kernel.comp_apply' _ _ _ hB,Kernel.comp_apply' _ _ _ hB]
    apply lintegral_congr_ae
    have hae : ∀ᵐ y ∂killedFirstPair z, y.2 ∉ returnSet := by
      rw [killedFirstPair,Kernel.restrict_apply]
      exact ae_restrict_mem (returnSet_measurable.compl.preimage measurable_snd)
    filter_upwards [hae] with y hy
    rw [witnessContinuation_outside_return y hy]
  rw [he,witnessRemaining,Kernel.comp_sum_left]
  apply congrArg Kernel.sum
  funext n
  rw [sourceWitnessTerm,sourceReturnTerm,Kernel.map_comp]

theorem sourceCycleWitness_series :
    sourceCycleWitnessKernel = Kernel.sum sourceWitnessTerm := by
  rw [sourceCycleWitnessKernel,← firstPairs_partition,Kernel.comp_add_right,
    witnessContinuation_comp_captured,witnessContinuation_comp_killed]
  ext z B hB
  rw [_root_.add_apply,Measure.add_apply,Kernel.sum_apply' _ _ hB,Kernel.sum_apply' _ _ hB]
  exact (tsum_eq_zero_add' (f := fun n : ℕ => sourceWitnessTerm n z B) ENNReal.summable).symm

lemma sourceWitnessTerm_duration (n : ℕ) (z : OddCost) :
    ∀ᵐ y ∂sourceWitnessTerm n z, y.2.1=2*(n+1) := by
  rw [sourceWitnessTerm,Kernel.map_apply _ (tagSourceReturn_measurable n)]
  apply (ae_map_iff (tagSourceReturn_measurable n).aemeasurable
    (measurableSet_eq_fun (measurable_fst.comp measurable_snd) measurable_const)).mpr
  exact Eventually.of_forall (fun _ => rfl)

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
