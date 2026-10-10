import OAI.NumberTheory.Jacobsthal.Partitions.CompletedParentInterval

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section


namespace NumberTheoryLean.ContinuousCompletedOccupation

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open _root_.Erdos970.Set _root_.Erdos970.Finset _root_.Erdos970.MeasureTheory
open scoped ENNReal
open FinitePathMeasures ContinuousKilledBins LowStateHorizon CemeteryKernel
open PairedCostGrouping OccupationDecomposition CostPrefixTransport

noncomputable abbrev liftReward := @CemeteryPowers.liftReward CostState

theorem liftReward_measurable {F : CostState → ℝ≥0∞} (hF : Measurable F) : Measurable (liftReward F) :=
  CemeteryPowers.liftReward_measurable hF

theorem completed_power_lift (v ell S : ℝ) {F : CostState → ℝ≥0∞} (hF : Measurable F)
    (n : ℕ) (q : Space CostState) :
    (∫⁻ y,liftReward F y ∂((continuousChain v ell S)^n) q) =
      liftReward (fun z => ∫⁻ y,F y ∂((lowKernel costKernel v ell S)^n) z) q :=
  CemeteryPowers.power_lift (lowKernel costKernel v ell S) hF n q

theorem low_power_integral_le (v ell S : ℝ) {F : CostState → ℝ≥0∞} (hF : Measurable F)
    (n : ℕ) (z : CostState) :
    (∫⁻ y,F y ∂((lowKernel costKernel v ell S)^n) z) ≤ ∫⁻ y,F y ∂(costKernel^n) z := by
  induction n generalizing z with
  | zero => exact le_rfl
  | succ n ih =>
    have hp : (lowKernel costKernel v ell S)^(n+1) =
        ((lowKernel costKernel v ell S)^n) ∘ₖ lowKernel costKernel v ell S := pow_succ _ _
    have hq : costKernel^(n+1) = (costKernel^n) ∘ₖ costKernel := pow_succ _ _
    rw [hp,hq,Kernel.lintegral_comp _ _ _ hF,Kernel.lintegral_comp _ _ _ hF]
    calc
      _ ≤ ∫⁻ y,∫⁻ a,F a ∂(costKernel^n) y ∂lowKernel costKernel v ell S z := lintegral_mono ih
      _ ≤ _ := by
        rw [lowKernel,Kernel.restrict_apply]
        exact setLIntegral_le_lintegral _ _

theorem inclusive_integral_eq_tsum {F : CostState → ℝ≥0∞} (hF : Measurable F) (z : CostState) :
    (∫⁻ y,F y ∂inclusiveOccupation z) = ∑' n : ℕ,∫⁻ y,F y ∂(costKernel^n) z := by
  rw [inclusiveOccupation,_root_.add_apply,lintegral_add_measure,Kernel.id_apply,
    lintegral_dirac' _ hF,fullOccupation,Kernel.sum_apply,lintegral_sum_measure]
  conv_rhs => rw [tsum_eq_zero_add' ENNReal.summable]
  congr 1
  change F z = ∫⁻ y,F y ∂Measure.dirac z
  rw [lintegral_dirac' _ hF]

theorem completed_finite_occupation_le (v ell S : ℝ) {F : CostState → ℝ≥0∞} (hF : Measurable F)
    (N : ℕ) (z : CostState) :
    (∑ n ∈ range N,∫⁻ y,liftReward F y ∂((continuousChain v ell S)^n) (.inl z)) ≤
      ∫⁻ y,F y ∂inclusiveOccupation z := by
  rw [inclusive_integral_eq_tsum hF z]
  calc
    _ ≤ ∑ n ∈ range N,∫⁻ y,F y ∂(costKernel^n) z := by
      apply Finset.sum_le_sum
      intro n _hn
      rw [completed_power_lift v ell S hF]
      exact low_power_integral_le v ell S hF n z
    _ ≤ _ := ENNReal.sum_le_tsum (range N)

end NumberTheoryLean.ContinuousCompletedOccupation

end

end Erdos970

end OAI
