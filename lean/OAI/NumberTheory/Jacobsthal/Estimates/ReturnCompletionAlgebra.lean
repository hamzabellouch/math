import OAI.NumberTheory.Jacobsthal.Renewal.RegenerationBandBounds

namespace OAI

namespace Erdos970


namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.TransitionKernels NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.CostReturnLaw NumberTheoryLean.CycleRegeneration
open NumberTheoryLean.InitialRegeneration

lemma firstReturn_succ_comp (n : ℕ) : firstReturn (n+1) = firstReturn n ∘ₖ costKilled := by
  unfold firstReturn
  rw [pow_succ]
  exact (Kernel.comp_assoc _ _ _).symm

lemma returnLaw_first_step : returnLaw = costCaptured + returnLaw ∘ₖ costKilled := by
  have hsplit : returnLaw = firstReturn 0+Kernel.sum (fun n => firstReturn (n+1)) := by
    ext z B hB
    rw [returnLaw,Kernel.sum_apply' _ _ hB,add_apply,Measure.add_apply,Kernel.sum_apply' _ _ hB]
    exact tsum_eq_zero_add' ENNReal.summable
  calc
    _ = firstReturn 0+Kernel.sum (fun n => firstReturn (n+1)) := hsplit
    _ = costCaptured+(Kernel.sum firstReturn) ∘ₖ costKilled := by
      congr 1
      · change costCaptured ∘ₖ (Kernel.id : Kernel OddCost OddCost) = costCaptured
        exact Kernel.comp_id _
      · rw [Kernel.comp_sum_left]
        apply congrArg Kernel.sum
        funext n
        exact firstReturn_succ_comp n
    _ = _ := rfl

lemma hitOrReturn_comp_captured : hitOrReturn ∘ₖ costCaptured = costCaptured := by
  classical
  have he : hitOrReturn ∘ₖ costCaptured = Kernel.id ∘ₖ costCaptured := by
    ext z B hB
    rw [Kernel.comp_apply' _ _ _ hB,Kernel.comp_apply' _ _ _ hB]
    apply lintegral_congr_ae
    have hae : ∀ᵐ y ∂costCaptured z, y ∈ returnSet := by
      rw [costCaptured,Kernel.restrict_apply]
      exact ae_restrict_mem returnSet_measurable
    filter_upwards [hae] with y hy
    rw [hitOrReturn,Kernel.piecewise_apply,ite_eq_left hy]
  simpa only [Kernel.id_comp] using he

lemma hitOrReturn_comp_killed : hitOrReturn ∘ₖ costKilled = returnLaw ∘ₖ costKilled := by
  classical
  ext z B hB
  rw [Kernel.comp_apply' _ _ _ hB,Kernel.comp_apply' _ _ _ hB]
  apply lintegral_congr_ae
  have hae : ∀ᵐ y ∂costKilled z, y ∉ returnSet := by
    rw [costKilled,Kernel.restrict_apply]
    exact ae_restrict_mem returnSet_measurable.compl
  filter_upwards [hae] with y hy
  rw [hitOrReturn,Kernel.piecewise_apply,ite_eq_right hy]

lemma complete_first_pair : hitOrReturn ∘ₖ pairedCostKernel = returnLaw := by
  rw [← costCaptured_add_costKilled,Kernel.comp_add_right,hitOrReturn_comp_captured,hitOrReturn_comp_killed]
  exact returnLaw_first_step.symm

lemma hitOrReturn_translation (z : OddCost) (a : ℝ) :
    (hitOrReturn z).map (shiftCost a) = hitOrReturn (shiftCost a z) := by
  classical
  have he : shiftCost a z ∈ returnSet ↔ z ∈ returnSet := Iff.rfl
  by_cases hz : z ∈ returnSet
  · rw [hitOrReturn,Kernel.piecewise_apply,ite_eq_left hz,Kernel.piecewise_apply,ite_eq_left (he.mpr hz),
      Kernel.id_apply,Kernel.id_apply]
    exact Measure.map_dirac' (shiftCost_measurable a) z
  · rw [hitOrReturn,Kernel.piecewise_apply,ite_eq_right hz,Kernel.piecewise_apply,
      ite_eq_right (fun h => hz (he.mp h))]
    exact returnLaw_translation z a

end Erdos970Dependency.MarkedVisits


end Erdos970

end OAI
