import OAI.NumberTheory.Jacobsthal.Probability.MarkedVisitGeometry

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.PairedCostGrouping

open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open TransitionKernels FinitePathGeometry FinitePathMeasures PairedCostProcess

def embedOdd (z : OddCost) : CostState := (.inr z.1, z.2)

theorem embedOdd_measurable : Measurable embedOdd :=
  (measurable_inr.comp measurable_fst).prodMk measurable_snd

theorem costKernel_eq_map (z : CostState) : costKernel z =
    (stateKernel z.1).map (fun s => (s, z.2 + cost (stateRatio s))) := by
  have hm : Measurable (fun s : State => (s, z.2 + cost (stateRatio s))) :=
    measurable_id.prodMk (measurable_const.add (cost_measurable.comp stateRatio_measurable))
  ext B hB
  rw [costKernel_apply _ hB, Measure.map_apply hm hB]
  rfl

theorem costKernel_odd_lintegral (s : OddState) (T : ℝ) {H : CostState → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ z, H z ∂costKernel (.inr s, T)) =
      ∫⁻ t : EvenState, H (.inl t, T + cost t.1) ∂oddToEven s := by
  have hm : Measurable (fun u : State => (u, T + cost (stateRatio u))) :=
    measurable_id.prodMk (measurable_const.add (cost_measurable.comp stateRatio_measurable))
  rw [costKernel_eq_map, lintegral_map hH hm]
  change (∫⁻ u, H (u, T + cost (stateRatio u)) ∂oddBranch s) = _
  rw [oddBranch, Kernel.map_apply _ measurable_inl,
    lintegral_map (f := fun u : State => H (u, T + cost (stateRatio u))) (hH.comp hm) measurable_inl]
  rfl

theorem costKernel_even_lintegral (s : EvenState) (T : ℝ) {H : CostState → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ z, H z ∂costKernel (.inl s, T)) =
      ∫⁻ t : OddState, H (.inr t, T + cost t.1) ∂evenToOdd s := by
  have hm : Measurable (fun u : State => (u, T + cost (stateRatio u))) :=
    measurable_id.prodMk (measurable_const.add (cost_measurable.comp stateRatio_measurable))
  rw [costKernel_eq_map, lintegral_map hH hm]
  change (∫⁻ u, H (u, T + cost (stateRatio u)) ∂evenBranch s) = _
  rw [evenBranch, Kernel.map_apply _ measurable_inr,
    lintegral_map (f := fun u : State => H (u, T + cost (stateRatio u))) (hH.comp hm) measurable_inr]
  rfl

theorem pairedCost_lintegral (z : OddCost) {H : OddCost → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ y, H y ∂pairedCostKernel z) =
      ∫⁻ t : EvenState, ∫⁻ u : OddState, H (u, z.2 + cost t.1 + cost u.1) ∂evenToOdd t ∂oddToEven z.1 := by
  have hm : Measurable (fun x : EvenState × OddState => (x.2, z.2 + cost x.1.1 + cost x.2.1)) :=
    measurable_snd.prodMk ((measurable_const.add (cost_measurable.comp (measurable_subtype_coe.comp measurable_fst))).add
      (cost_measurable.comp (measurable_subtype_coe.comp measurable_snd)))
  have heq : pairedCostKernel z = (pairedDraws z.1).map (fun x => (x.2, z.2 + cost x.1.1 + cost x.2.1)) := by
    ext B hB
    rw [pairedCostKernel_apply _ hB, Measure.map_apply hm hB]
    rfl
  rw [heq, lintegral_map hH hm, pairedDraws,
    Kernel.lintegral_compProd _ _ _ (f := fun x : EvenState × OddState => H (x.2, z.2 + cost x.1.1 + cost x.2.1)) (hH.comp hm)]
  rfl

theorem pairedCost_full_grouping (z : OddCost) :
    (pairedCostKernel z).map embedOdd = (costKernel ^ 2) (embedOdd z) := by
  apply Measure.ext_of_lintegral
  intro H hH
  have hp : costKernel ^ 2 = costKernel ∘ₖ costKernel := by
    rw [pow_two]
    rfl
  rw [lintegral_map hH embedOdd_measurable,
    pairedCost_lintegral z (H := fun x => H (embedOdd x)) (hH.comp embedOdd_measurable),
    hp, Kernel.lintegral_comp _ _ _ hH]
  have hJ : Measurable (fun y : CostState => ∫⁻ w, H w ∂costKernel y) := hH.lintegral_kernel
  change (∫⁻ t : EvenState, ∫⁻ u : OddState, H (.inr u, z.2 + cost t.1 + cost u.1) ∂evenToOdd t ∂oddToEven z.1) = _
  simp only [embedOdd]
  rw [costKernel_odd_lintegral z.1 z.2 (H := fun y : CostState => ∫⁻ w, H w ∂costKernel y) hJ]
  apply lintegral_congr
  intro t
  exact (costKernel_even_lintegral t (z.2 + cost t.1) hH).symm

end NumberTheoryLean.PairedCostGrouping

end

end Erdos970

end OAI
