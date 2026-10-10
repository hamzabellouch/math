import OAI.NumberTheory.Jacobsthal.Renewal.MarkedCycleCompletion

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.PairedCostProcess NumberTheoryLean.CostReturnLaw
open NumberTheoryLean.RegenerationTails NumberTheoryLean.CycleCostLower
open NumberTheoryLean.CycleCostMoments

noncomputable def sourceCycleLaw : Measure MarkedOddCost := completedMarkedKernel (regenerationState,0)

instance sourceCycleLaw_isProbabilityMeasure : IsProbabilityMeasure sourceCycleLaw := by
  unfold sourceCycleLaw
  infer_instance

def sourceMarkSet : Set MarkedOddCost := {z | z.1=true}

lemma sourceMarkSet_measurable : MeasurableSet sourceMarkSet :=
  measurable_fst (measurableSet_singleton true)

def sourceCostProjection (z : MarkedOddCost) : ℝ := z.2.2

lemma sourceCostProjection_measurable : Measurable sourceCostProjection :=
  measurable_snd.comp measurable_snd

lemma sourceCycle_cost_projection : sourceCycleLaw.map sourceCostProjection = cycleCostLaw := by
  rw [cycleCostLaw,← completedMarked_forget (regenerationState,0),
    Measure.map_map measurable_snd measurable_snd]
  rfl

lemma sourceCycle_mark_mass : sourceCycleLaw sourceMarkSet = markProbability :=
  completedMarked_mark_mass regenerationState (by norm_num [regenerationState]) 0

noncomputable def markedCostLaw : Measure ℝ :=
  (sourceCycleLaw.restrict sourceMarkSet).map sourceCostProjection

noncomputable def unmarkedCostLaw : Measure ℝ :=
  (sourceCycleLaw.restrict sourceMarkSetᶜ).map sourceCostProjection

instance markedCostLaw_isFiniteMeasure : IsFiniteMeasure markedCostLaw := by
  unfold markedCostLaw
  infer_instance

instance unmarkedCostLaw_isFiniteMeasure : IsFiniteMeasure unmarkedCostLaw := by
  unfold unmarkedCostLaw
  infer_instance

lemma markedCostLaw_add_unmarked : markedCostLaw+unmarkedCostLaw = cycleCostLaw := by
  calc
    _ = (sourceCycleLaw.restrict sourceMarkSet+sourceCycleLaw.restrict sourceMarkSetᶜ).map sourceCostProjection :=
      (Measure.map_add _ _ sourceCostProjection_measurable).symm
    _ = sourceCycleLaw.map sourceCostProjection := by rw [Measure.restrict_add_restrict_compl sourceMarkSet_measurable]
    _ = _ := sourceCycle_cost_projection

lemma markedCostLaw_mass : markedCostLaw univ = markProbability := by
  rw [markedCostLaw,Measure.map_apply sourceCostProjection_measurable MeasurableSet.univ,
    preimage_univ,Measure.restrict_apply MeasurableSet.univ,univ_inter]
  exact sourceCycle_mark_mass

lemma unmarkedCostLaw_mass : unmarkedCostLaw univ = 1-markProbability := by
  rw [unmarkedCostLaw,Measure.map_apply sourceCostProjection_measurable MeasurableSet.univ,
    preimage_univ,Measure.restrict_apply MeasurableSet.univ,univ_inter,
    measure_compl sourceMarkSet_measurable (measure_ne_top _ _),measure_univ,sourceCycle_mark_mass]

lemma markedCostLaw_le : markedCostLaw ≤ cycleCostLaw := by
  rw [← markedCostLaw_add_unmarked]
  exact Measure.le_add_right le_rfl

lemma unmarkedCostLaw_le : unmarkedCostLaw ≤ cycleCostLaw := by
  rw [← markedCostLaw_add_unmarked]
  exact Measure.le_add_left le_rfl

lemma source_marked_cost_lower : ∀ᵐ G ∂markedCostLaw, Real.log (4/3) ≤ G :=
  (ae_mono markedCostLaw_le) cycleCostLaw_lower

lemma source_unmarked_cost_lower : ∀ᵐ G ∂unmarkedCostLaw, Real.log (4/3) ≤ G :=
  (ae_mono unmarkedCostLaw_le) cycleCostLaw_lower

lemma source_marked_exponential_moments : ∃ eta : ℝ, 0 < eta ∧
    (∫⁻ G, ENNReal.ofReal (Real.exp (eta*G)) ∂markedCostLaw) < ∞ ∧
    (∫⁻ G, ENNReal.ofReal (Real.exp (eta*G)) ∂unmarkedCostLaw) < ∞ := by
  obtain ⟨eta,heta,hfin⟩ := cycle_cost_exponential_moment
  exact ⟨eta,heta,(lintegral_mono' markedCostLaw_le le_rfl).trans_lt hfin,
    (lintegral_mono' unmarkedCostLaw_le le_rfl).trans_lt hfin⟩

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
