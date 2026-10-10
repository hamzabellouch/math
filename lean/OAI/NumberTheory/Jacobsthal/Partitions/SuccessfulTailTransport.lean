import OAI.NumberTheory.Jacobsthal.Paths.ContinuousArrivalSupport

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.SuccessfulTailTransport

open _root_.Set _root_.Finset _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ActualProcessCoupling PersistentFailureFlag ActualFlagInvariant
open RegeneratingInverseBands InvariantInverseWeights ArrivalKernelGeometry
open SuccessfulRewardComparison ContinuousArrivalSupport ContinuousCompletedOccupation
open ContinuousKilledBins CostPrefixTransport

variable {w ell S : ℝ} {start : Node}

noncomputable def cleanReward (c K : ℝ) (q : FlagState (JointState w ell S start)) : ℝ≥0∞ :=
  if q.2 = false then PrimeExponentialTail.tailReward c K q.1.1 else 0

theorem cleanReward_measurable (c K : ℝ) : Measurable (cleanReward (w:=w) (ell:=ell) (S:=S) (start:=start) c K) := by
  apply Measurable.ite (measurable_snd (measurableSet_singleton false))
  · exact (measurable_of_countable (PrimeExponentialTail.tailReward c K)).comp (measurable_fst.comp measurable_fst)
  · exact measurable_const

theorem positive_completed_occupation_le (v ell S : ℝ) {F : CostState → ℝ≥0∞} (hF : Measurable F)
    (N : ℕ) (z : CostState) :
    (∑ n ∈ range N,∫⁻ y,liftReward F y ∂((continuousChain v ell S)^(n+1)) (.inl z)) ≤
      ∫⁻ y,F y ∂inclusiveOccupation z := by
  refine le_trans ?_ (completed_finite_occupation_le v ell S hF (N+1) z)
  rw [Finset.sum_range_succ']
  exact le_add_of_nonneg_right zero_le

theorem actual_clean_tail_transport : ∃ L : ℝ,0 < L ∧
    ∀ w ell S : ℝ,∀ start : Node,∀ _hw : normalizationThreshold ≤ w,
      ∀ _hell : 1 ≤ ell,∀ _hS0 : 0 ≤ S,∀ _hS : S ≤ (Real.log w)^3,
      ∀ _hr : 0 < start.gap,∀ hs : Valid start.side start.ratio,∀ _hsS : start.ratio ≤ S,
      3 ≤ S → ∀ mesh : ℝ,0 < mesh → ∀ N : ℕ,
        4*(N:ℝ)*mesh ≤ 1 → L*(1+S)^3*mesh ≤ 1 → ∀ M : ℕ,∀ c : ℝ,0 < c →
        (∑ n ∈ range N,∫⁻ q,cleanReward c (3*((M:ℝ)+1)) q
          ∂CouplingData.sourceLaw w ell S start hs mesh (n+1)) ≤
          ENNReal.ofReal 27*(∫⁻ z,WeightedGapTail.tailReward (c/3) (Real.log start.gap) ell M z
            ∂inclusiveOccupation (FlaggedSourceStart.sourceCostState hs)) := by
  obtain ⟨L,hL,hcompare⟩ := actual_good_tail_comparison
  refine ⟨L,hL,?_⟩
  intro w ell S start hw hell hS0 hS hr hs hsS hS3 mesh hm N hclock hsmall M c hc
  let F := WeightedGapTail.tailReward (c/3) (Real.log start.gap) ell M
  have hF : Measurable F := WeightedGapTail.tailReward_measurable _ _ _ _
  have hpoint : ∀ n,1 ≤ n → n ≤ N →
      ∀ᵐ q ∂CouplingData.sourceLaw w ell S start hs mesh n,
        cleanReward c (3*((M:ℝ)+1)) q ≤ ENNReal.ofReal 27*liftReward F q.1.2 := by
    intro n hn hnN
    have hg := FlaggedSourceStart.sourceLaw_good hw hell hS0 hS hr hs hsS hm n
    rw [CouplingData.sourceLaw_eq hw hell hS0 hS hr hs hsS] at hg
    filter_upwards [hg,source_arrival hw hell hS0 hS hr hs hsS mesh n hn] with q hgood harr
    by_cases hb : q.2 = false
    · have hgood := hgood hb
      rw [cleanReward,ite_eq_left hb]
      rcases q with ⟨⟨p,y⟩,b⟩
      cases p with
      | none => exact zero_le
      | some h =>
        cases y with
        | inr u => exact False.elim hgood
        | inl z =>
          have hnum : 4*(n:ℝ)*mesh ≤ 1 := by
            have hnR : (n:ℝ) ≤ (N:ℝ) := by exact_mod_cast hnN
            exact (mul_le_mul_of_nonneg_right (by linarith : 4*(n:ℝ) ≤ 4*(N:ℝ)) hm.le).trans hclock
          exact hcompare w ell S hell hS3 start hr hs hsS (Real.log start.gap) mesh n M hnum hsmall h z hgood harr c hc
    · rw [cleanReward,ite_eq_right hb]
      exact zero_le
  have hone : ∀ n,1 ≤ n → n ≤ N →
      (∫⁻ q,cleanReward c (3*((M:ℝ)+1)) q ∂CouplingData.sourceLaw w ell S start hs mesh n) ≤
        ENNReal.ofReal 27*(∫⁻ y,liftReward F y
          ∂((continuousChain (Real.log start.gap) ell S)^n) (.inl (FlaggedSourceStart.sourceCostState hs))) := by
    intro n hn hnN
    have he := FlaggedSourceStart.sourceLaw_continuous hw hell hS0 hS hr hs hsS mesh n
    rw [CouplingData.sourceLaw_eq hw hell hS0 hS hr hs hsS] at he
    calc
      _ ≤ ∫⁻ q,ENNReal.ofReal 27*liftReward F q.1.2 ∂CouplingData.sourceLaw w ell S start hs mesh n :=
        lintegral_mono_ae (hpoint n hn hnN)
      _ = _ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,← he,
          lintegral_map (g := fun q : FlagState (JointState w ell S start) => q.1.2) (liftReward_measurable hF) (measurable_snd.comp measurable_fst)]
  calc
    _ ≤ ∑ n ∈ range N,ENNReal.ofReal 27*(∫⁻ y,liftReward F y
        ∂((continuousChain (Real.log start.gap) ell S)^(n+1)) (.inl (FlaggedSourceStart.sourceCostState hs))) := by
      apply Finset.sum_le_sum
      intro n hn
      exact hone (n+1) (by omega) (by have hh := Finset.mem_range.mp hn; omega)
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (positive_completed_occupation_le _ _ _ hF N _) zero_le

end NumberTheoryLean.SuccessfulTailTransport

end

end Erdos970

end OAI
