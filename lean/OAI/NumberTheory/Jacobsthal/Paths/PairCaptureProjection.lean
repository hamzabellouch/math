import OAI.NumberTheory.Jacobsthal.Estimates.FullReturnCylinders

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory Function Preorder
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.PairedCostGrouping NumberTheoryLean.FirstHitKernels
open NumberTheoryLean.CostReturnLaw

def rawLast (n : ℕ) (h : RawHistory n) : CostState := h ⟨n,by simp⟩

lemma rawLast_measurable (n : ℕ) : Measurable (rawLast n) := measurable_pi_apply _

lemma rawExtension_last_pair (n : ℕ) (h : RawHistory n) :
    (rawExtension n (n+2) h).map (rawLast (n+2)) = (costKernel ^ 2) (rawLast n h) := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF (rawLast_measurable _)]
  have he := congrArg (fun μ : Measure (CostState × CostState) => ∫⁻ p, F p.2 ∂μ)
    (conditional_pair_trace n h)
  rw [lintegral_map (f := fun p : CostState × CostState => F p.2) (hF.comp measurable_snd)
    (nextPairEval_measurable n),fullPairTraceKernel,
    Kernel.lintegral_compProd _ _ _ (f := fun p : CostState × CostState => F p.2) (hF.comp measurable_snd)] at he
  rw [pow_two]
  change (∫⁻ z, F (rawLast (n+2) z) ∂rawExtension n (n+2) h) =
    ∫⁻ y, F y ∂(costKernel ∘ₖ costKernel) (rawLast n h)
  rw [Kernel.lintegral_comp _ _ _ hF]
  exact he

lemma rawExtension_restricted_last_pair (n : ℕ) (h : RawHistory n)
    {E : Set CostState} (hE : MeasurableSet E) :
    (((rawExtension n (n+2)).restrict (hE.preimage (rawLast_measurable (n+2)))) h).map (rawLast (n+2)) =
      ((costKernel ^ 2) (rawLast n h)).restrict E := by
  rw [Kernel.restrict_apply,← Measure.restrict_map (rawLast_measurable _) hE,rawExtension_last_pair]

noncomputable def fullPairCaptured : Kernel CostState CostState :=
  (costKernel ^ 2).restrict regenerationSet_measurable

noncomputable def fullPairKilled : Kernel CostState CostState :=
  (costKernel ^ 2).restrict regenerationSet_measurable.compl

instance fullPairCaptured_isFiniteKernel : IsFiniteKernel fullPairCaptured := by
  have : IsFiniteKernel (costKernel ^ 2) := by rw [pow_two]; change IsFiniteKernel (costKernel ∘ₖ costKernel); infer_instance
  unfold fullPairCaptured
  infer_instance

instance fullPairKilled_isFiniteKernel : IsFiniteKernel fullPairKilled := by
  have : IsFiniteKernel (costKernel ^ 2) := by rw [pow_two]; change IsFiniteKernel (costKernel ∘ₖ costKernel); infer_instance
  unfold fullPairKilled
  infer_instance

lemma embedOdd_regeneration_preimage : embedOdd ⁻¹' regenerationSet = returnSet := rfl

lemma costCaptured_fullPair_projection (z : OddCost) :
    (costCaptured z).map embedOdd = fullPairCaptured (embedOdd z) := by
  rw [costCaptured,Kernel.restrict_apply,fullPairCaptured,Kernel.restrict_apply,
    ← embedOdd_regeneration_preimage,← Measure.restrict_map embedOdd_measurable regenerationSet_measurable,
    pairedCost_full_grouping]

lemma costKilled_fullPair_projection (z : OddCost) :
    (costKilled z).map embedOdd = fullPairKilled (embedOdd z) := by
  rw [costKilled,Kernel.restrict_apply,fullPairKilled,Kernel.restrict_apply,
    ← embedOdd_regeneration_preimage,← preimage_compl,
    ← Measure.restrict_map embedOdd_measurable regenerationSet_measurable.compl,pairedCost_full_grouping]

lemma rawCapturedPair_projection (n : ℕ) (h : RawHistory n) :
    ((((rawExtension n (n+2)).restrict (lastRegeneration_measurable (n+2))) h).map (rawLast (n+2))) =
      fullPairCaptured (rawLast n h) := by
  exact rawExtension_restricted_last_pair n h regenerationSet_measurable

lemma rawKilledPair_projection (n : ℕ) (h : RawHistory n) :
    ((((rawExtension n (n+2)).restrict (lastRegeneration_measurable (n+2)).compl) h).map (rawLast (n+2))) =
      fullPairKilled (rawLast n h) := by
  exact rawExtension_restricted_last_pair n h regenerationSet_measurable.compl

lemma firstReturnHistory_zero (a : ℕ) :
    firstReturnHistory a 0 = (rawExtension a (a+2)).restrict (lastRegeneration_measurable (a+2)) := by
  ext h : 1
  rw [firstReturnHistory,Kernel.restrict_apply,Kernel.restrict_apply]
  congr 1
  ext z
  simp [avoidOddReturns]

theorem firstReturnHistory_zero_projection (a : ℕ) (h : RawHistory a) (z : OddCost)
    (hz : rawLast a h=embedOdd z) :
    (firstReturnHistory a 0 h).map (rawLast (a+2)) = (firstReturn 0 z).map embedOdd := by
  rw [firstReturnHistory_zero,rawCapturedPair_projection,hz,← costCaptured_fullPair_projection]
  have he : firstReturn 0 = costCaptured := Kernel.comp_id _
  rw [he]

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
