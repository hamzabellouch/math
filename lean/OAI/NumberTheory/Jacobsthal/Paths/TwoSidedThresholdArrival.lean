import OAI.NumberTheory.Jacobsthal.Estimates.TwoSidedThresholdHazard

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.TwoSidedThresholdArrival
open _root_.Set _root_.MeasureTheory ProbabilityTheory
open FinitePathGeometry FinitePathMeasures TransitionKernels ArrivalKernelGeometry RegeneratingInverseBands
open TwoSidedThresholdGeometry TwoSidedThresholdKernel TwoSidedThresholdHazard
open RepresentativeStopGeometry ActualCouplingUpdates

noncomputable def reconstructedParent (v : ℝ) (y : CostState) : ℝ := gapValue v y+currentExponent v y

theorem reconstructedParent_measurable (v : ℝ) : Measurable (reconstructedParent v) :=
  (gapValue_measurable v).add (currentExponent_measurable v)

theorem reconstructedParent_update (v : ℝ) (z : CostState) (s : State) :
    reconstructedParent v (s,z.2+cost (stateRatio s))=gapValue v z := by
  rw [reconstructedParent,gapValue_update,currentExponent_update]
  exact gap_exponent_conservation (valid_pos (stateRatio_valid s))

theorem reconstructed_geometry (v : ℝ) (y : CostState) :
    nextExponent (reconstructedParent v y) (stateRatio y.1)=currentExponent v y ∧
    nextGap (reconstructedParent v y) (stateRatio y.1)=gapValue v y := by
  have ht := valid_pos (stateRatio_valid y.1)
  constructor
  · unfold nextExponent reconstructedParent currentExponent
    field_simp [ht.ne',show stateRatio y.1+1 ≠ 0 by positivity]
  · unfold nextGap reconstructedParent currentExponent
    field_simp [ht.ne',show stateRatio y.1+1 ≠ 0 by positivity]

noncomputable def thickArrival (v d e : ℝ) : Set CostState :=
  {y | stateSide y.1=.even ∧ 3 ≤ reconstructedParent v y ∧
    stateRatio y.1 ∈ thickStrip (reconstructedParent v y) (d/reconstructedParent v y+e)}

theorem thickArrival_measurable (v d e : ℝ) : MeasurableSet (thickArrival v d e) := by
  have hr := reconstructedParent_measurable v
  have ht : Measurable (fun y : CostState => stateRatio y.1) := stateRatio_measurable.comp measurable_fst
  have hs : Measurable (fun y : CostState => normalizedSlack (reconstructedParent v y) (stateRatio y.1)) := by
    unfold normalizedSlack ErdosEvenThreshold.thresholdSlack nextGap nextExponent
    exact (((hr.mul ht).div (ht.add_const 1)).sub
      (((measurable_const.mul (hr.div (ht.add_const 1)))).max ((hr.div (ht.add_const 1)).add_const 2))).div hr
  exact (measurable_fst (side_set_measurable .even)).inter
    ((measurableSet_le measurable_const hr).inter
      ((measurableSet_le measurable_const ht).inter ((measurableSet_le ht measurable_const).inter
        (measurableSet_le hs.abs ((measurable_const.div hr).add_const e)))))

theorem thickArrival_update (v d e : ℝ) (z : CostState) (s : State) :
    (s,z.2+cost (stateRatio s)) ∈ thickArrival v d e ↔ stateSide s=.even ∧
      3 ≤ gapValue v z ∧ stateRatio s ∈ thickStrip (gapValue v z) (d/gapValue v z+e) := by
  change stateSide s=.even ∧ _ ↔ _
  rw [reconstructedParent_update]

theorem thickHazard_eq_actual (v d e : ℝ) (z : CostState) :
    thickHazard (gapValue v z) d e z.1=(costKernel z (thickArrival v d e)).toReal := by
  rw [costKernel_apply z (thickArrival_measurable v d e)]
  rcases z with ⟨s,T⟩
  cases s with
  | inl s =>
    change 0=(evenBranch s {t | (t,T+cost (stateRatio t)) ∈ thickArrival v d e}).toReal
    rw [evenBranch,Kernel.map_apply' _ measurable_inr _]
    · have he : Sum.inr ⁻¹' {t : State | (t,T+cost (stateRatio t)) ∈ thickArrival v d e}=∅ := by
        ext t
        change (Sum.inr t,T+cost (stateRatio (Sum.inr t))) ∈ thickArrival v d e ↔ False
        rw [thickArrival_update v d e ((Sum.inl s),T)]
        simp [stateSide]
      rw [he,measure_empty,ENNReal.toReal_zero]
    · exact (measurable_id.prodMk
        (measurable_const.add (cost_measurable.comp stateRatio_measurable))) (thickArrival_measurable v d e)
  | inr s =>
    change _=(oddBranch s {t | (t,T+cost (stateRatio t)) ∈ thickArrival v d e}).toReal
    rw [oddBranch,Kernel.map_apply' _ measurable_inl _]
    · by_cases hR : 3 ≤ gapValue v ((Sum.inr s),T)
      · have he : Sum.inl ⁻¹' {t : State | (t,T+cost (stateRatio t)) ∈ thickArrival v d e}=
            (Subtype.val : EvenState → ℝ) ⁻¹' thickStrip (gapValue v ((Sum.inr s),T)) (d/gapValue v ((Sum.inr s),T)+e) := by
          ext t
          change (Sum.inl t,T+cost (stateRatio (Sum.inl t))) ∈ thickArrival v d e ↔ _
          rw [thickArrival_update v d e ((Sum.inr s),T)]
          simp only [stateSide,stateRatio,Sum.elim_inl,hR,true_and,Set.mem_preimage]
        rw [he,thickHazard,ite_eq_left hR]
      · have he : Sum.inl ⁻¹' {t : State | (t,T+cost (stateRatio t)) ∈ thickArrival v d e}=∅ := by
          ext t
          change (Sum.inl t,T+cost (stateRatio (Sum.inl t))) ∈ thickArrival v d e ↔ False
          rw [thickArrival_update v d e ((Sum.inr s),T)]
          simp only [hR,false_and,and_false]
        rw [he,measure_empty,ENNReal.toReal_zero,thickHazard,ite_eq_right hR]
    · exact (measurable_id.prodMk
        (measurable_const.add (cost_measurable.comp stateRatio_measurable))) (thickArrival_measurable v d e)
end NumberTheoryLean.TwoSidedThresholdArrival

end

end Erdos970

end OAI
