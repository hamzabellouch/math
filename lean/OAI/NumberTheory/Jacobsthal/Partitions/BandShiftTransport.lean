import OAI.NumberTheory.Jacobsthal.Paths.CostPrefixTransport

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.BandShiftTransport

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open FinitePathMeasures OccupationRegeneration RegenerationBandBounds CostPrefixTransport

noncomputable def bandExpectation (Q : State → ℝ≥0∞) (v h : ℝ) (z : CostState) : ℝ≥0∞ :=
  ∫⁻ y, stateBandReward Q v h y ∂inclusiveOccupation z

noncomputable def zeroBandExpectation (Q : State → ℝ≥0∞) (v h : ℝ) (s : State) : ℝ≥0∞ :=
  bandExpectation Q v h (s, 0)

theorem stateBandReward_measurable {Q : State → ℝ≥0∞} (hQ : Measurable Q) (v h : ℝ) :
    Measurable (stateBandReward Q v h) :=
  (hQ.comp measurable_fst).indicator (measurable_snd measurableSet_Icc)

theorem bandExpectation_measurable {Q : State → ℝ≥0∞} (hQ : Measurable Q) (v h : ℝ) :
    Measurable (bandExpectation Q v h) := (stateBandReward_measurable hQ v h).lintegral_kernel

theorem zeroBandExpectation_measurable {Q : State → ℝ≥0∞} (hQ : Measurable Q) (v h : ℝ) :
    Measurable (zeroBandExpectation Q v h) :=
  (bandExpectation_measurable hQ v h).comp (measurable_id.prodMk measurable_const)

theorem stateBandReward_shift (Q : State → ℝ≥0∞) (v h a : ℝ) (y : CostState) :
    stateBandReward Q v h (shiftFullCost a y) = stateBandReward Q (v - a) h y := by
  classical
  have heq : y.2 + a ∈ Icc v (v + h) ↔ y.2 ∈ Icc (v - a) (v - a + h) := by
    simp only [mem_Icc]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  simp only [stateBandReward, indicator_apply, mem_preimage, shiftFullCost]
  simp only [heq]

theorem bandExpectation_translation {Q : State → ℝ≥0∞} (hQ : Measurable Q)
    (v h : ℝ) (z : CostState) :
    bandExpectation Q v h z = zeroBandExpectation Q (v - z.2) h z.1 := by
  have hshift := inclusiveOccupation_translation (z.1, 0) z.2
  have hz : shiftFullCost z.2 (z.1, 0) = z := by simp [shiftFullCost]
  rw [hz] at hshift
  rw [bandExpectation, ← hshift, lintegral_map (stateBandReward_measurable hQ v h) (shiftFullCost_measurable z.2)]
  apply lintegral_congr
  intro y
  exact stateBandReward_shift Q v h z.2 y

theorem stateBandReward_mono (Q : State → ℝ≥0∞) {v h v' h' : ℝ}
    (hsub : Icc v (v + h) ⊆ Icc v' (v' + h')) (y : CostState) :
    stateBandReward Q v h y ≤ stateBandReward Q v' h' y := by
  classical
  unfold stateBandReward
  by_cases hy : y.2 ∈ Icc v (v + h)
  · rw [indicator_of_mem (show y ∈ Prod.snd ⁻¹' Icc v (v + h) from hy),
      indicator_of_mem (show y ∈ Prod.snd ⁻¹' Icc v' (v' + h') from hsub hy)]
  · rw [indicator_of_notMem (show y ∉ Prod.snd ⁻¹' Icc v (v + h) from hy)]
    exact zero_le

theorem bandExpectation_mono (Q : State → ℝ≥0∞) {v h v' h' : ℝ}
    (hsub : Icc v (v + h) ⊆ Icc v' (v' + h')) (z : CostState) :
    bandExpectation Q v h z ≤ bandExpectation Q v' h' z :=
  lintegral_mono (stateBandReward_mono Q hsub)

theorem remove_prefix_cost {Q : State → ℝ≥0∞} (hQ : Measurable Q)
    (v h C : ℝ) (z : CostState) (hz : 0 ≤ z.2 ∧ z.2 ≤ C) :
    bandExpectation Q v h z ≤ zeroBandExpectation Q (v - C) (h + C) z.1 := by
  rw [bandExpectation_translation hQ]
  apply bandExpectation_mono
  intro t ht
  change v - z.2 ≤ t ∧ t ≤ v - z.2 + h at ht
  change v - C ≤ t ∧ t ≤ v - C + (h + C)
  constructor <;> linarith [ht.1, ht.2, hz.1, hz.2]

theorem restore_prefix_cost {Q : State → ℝ≥0∞} (hQ : Measurable Q)
    (v h C : ℝ) (z : CostState) (hz : 0 ≤ z.2 ∧ z.2 ≤ C) :
    zeroBandExpectation Q v h z.1 ≤ bandExpectation Q v (h + C) z := by
  rw [bandExpectation_translation hQ]
  apply bandExpectation_mono
  intro t ht
  change v ≤ t ∧ t ≤ v + h at ht
  change v - z.2 ≤ t ∧ t ≤ v - z.2 + (h + C)
  constructor <;> linarith [ht.1, ht.2, hz.1, hz.2]

theorem prefix_band_domination {Q : State → ℝ≥0∞} (hQ : Measurable Q)
    (m n : ℕ) (x y : State) {C : ℝ≥0∞}
    (hdom : (stateKernel ^ m) x ≤ C • (stateKernel ^ n) y) (v h : ℝ) :
    (∫⁻ z, stateBandReward Q v h z ∂prefixOccupation m (x, 0)) ≤
      C * ∫⁻ z, stateBandReward Q (v - (m : ℝ) * Real.log 3)
        (h + (m : ℝ) * Real.log 3 + (n : ℝ) * Real.log 3) z ∂prefixOccupation n (y, 0) := by
  let v' := v - (m : ℝ) * Real.log 3
  let h' := h + (m : ℝ) * Real.log 3
  have hM := zeroBandExpectation_measurable hQ v' h'
  have hmCost : ∀ᵐ z ∂(costKernel ^ m) (x, 0), 0 ≤ z.2 ∧ z.2 ≤ (m : ℝ) * Real.log 3 := by
    simpa only [zero_add] using costKernel_pow_cost_bounds m (x, 0)
  have hnCost : ∀ᵐ z ∂(costKernel ^ n) (y, 0), 0 ≤ z.2 ∧ z.2 ≤ (n : ℝ) * Real.log 3 := by
    simpa only [zero_add] using costKernel_pow_cost_bounds n (y, 0)
  rw [prefixOccupation, Kernel.lintegral_comp _ _ _ (stateBandReward_measurable hQ v h),
    prefixOccupation, Kernel.lintegral_comp _ _ _ (stateBandReward_measurable hQ v' (h' + (n : ℝ) * Real.log 3))]
  change (∫⁻ z, bandExpectation Q v h z ∂(costKernel ^ m) (x, 0)) ≤
    C * ∫⁻ z, bandExpectation Q v' (h' + (n : ℝ) * Real.log 3) z ∂(costKernel ^ n) (y, 0)
  calc
    _ ≤ ∫⁻ z, zeroBandExpectation Q v' h' z.1 ∂(costKernel ^ m) (x, 0) := by
      apply lintegral_mono_ae
      filter_upwards [hmCost] with z hz
      exact remove_prefix_cost hQ v h ((m : ℝ) * Real.log 3) z hz
    _ = ∫⁻ s, zeroBandExpectation Q v' h' s ∂(stateKernel ^ m) x := by
      rw [← costKernel_pow_map_state m (x, 0), lintegral_map hM measurable_fst]
    _ ≤ ∫⁻ s, zeroBandExpectation Q v' h' s ∂C • (stateKernel ^ n) y := lintegral_mono' hdom le_rfl
    _ = C * ∫⁻ s, zeroBandExpectation Q v' h' s ∂(stateKernel ^ n) y := by rw [lintegral_smul_measure, smul_eq_mul]
    _ = C * ∫⁻ z, zeroBandExpectation Q v' h' z.1 ∂(costKernel ^ n) (y, 0) := by
      rw [← costKernel_pow_map_state n (y, 0), lintegral_map hM measurable_fst]
    _ ≤ _ := by
      apply mul_le_mul le_rfl _ zero_le zero_le
      apply lintegral_mono_ae
      filter_upwards [hnCost] with z hz
      exact restore_prefix_cost hQ v' h' ((n : ℝ) * Real.log 3) z hz

end NumberTheoryLean.BandShiftTransport

end

end Erdos970

end OAI
