import OAI.NumberTheory.Jacobsthal.Sieve.PrimeExponentialTail

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.SuccessfulRewardComparison

open _root_.Set _root_.MeasureTheory
open scoped ENNReal
open FinitePathGeometry FinitePathMeasures PrimeHistories PrimeKilledChain
open ActualFlagInvariant GridWeightComparison DerivativeWeights
open RegeneratingInverseBands InvariantInverseWeights ArrivalKernelGeometry

theorem nearby_inverse_ratio : ∃ L : ℝ,0 < L ∧ ∀ S : ℝ,3 ≤ S →
    ∀ i : Side,∀ a b h : ℝ,Valid i a → Valid i b → a ≤ S → b ≤ S →
      |a-b| ≤ h → L*(1+S)^3*h ≤ 1 → weight i b/weight i a ≤ 3 := by
  obtain ⟨L,hL,hlocal⟩ := weight_local_ratio
  refine ⟨L,hL,?_⟩
  intro S hS i a b h ha hb haS hbS hab hsmall
  by_cases hba : b ≤ a
  · have hah : a ≤ b+h := by linarith [(abs_le.mp hab).2]
    exact (hlocal S hS i b a h hb ha haS hba hah).trans
      ((Real.exp_le_exp.mpr hsmall).trans Real.exp_one_lt_three.le)
  · have hmono := TwoStepDensityBounds.weight_antitone ha hb (le_of_not_ge hba)
    have hratio : weight i b/weight i a ≤ 1 := (div_le_one (weight_pos ha)).mpr hmono
    linarith

theorem reward_factor_comparison {c r q φ ψ : ℝ} (hc : 0 < c) (hr : 0 < r) (hq : 0 < q)
    (hφ : 0 < φ) (hψ : 0 < ψ) (hrq : r ≤ 3*q) (hqr : q ≤ 3*r) (hw : ψ/φ ≤ 3) :
    r^2*Real.exp (-c*r)/φ ≤ 27*(q^2*Real.exp (-(c/3)*q)/ψ) := by
  have hsq : r^2 ≤ 9*q^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hrq) (show 0 ≤ 3*q+r by linarith)]
  have he : Real.exp (-c*r) ≤ Real.exp (-(c/3)*q) := Real.exp_le_exp.mpr (by nlinarith)
  have hInv : 1/φ ≤ 3/ψ := by
    apply (div_le_div_iff₀ hφ hψ).mpr
    have hh := (div_le_iff₀ hφ).mp hw
    simpa only [one_mul] using hh
  calc
    _ = (r^2*Real.exp (-c*r))*(1/φ) := by ring
    _ ≤ ((9*q^2)*Real.exp (-(c/3)*q))*(3/ψ) :=
      mul_le_mul (mul_le_mul hsq he (Real.exp_pos _).le (by positivity)) hInv
        (one_div_pos.mpr hφ).le (by positivity)
    _ = _ := by ring

theorem stateWeight_eq (s : State) : stateWeight s = weight (stateSide s) (stateRatio s) := by
  cases s <;> rfl

theorem actual_good_tail_comparison : ∃ L : ℝ,0 < L ∧
    ∀ w ell S : ℝ,1 ≤ ell → 3 ≤ S → ∀ start : Node,
      0 < start.gap → Valid start.side start.ratio → start.ratio ≤ S →
      ∀ v mesh : ℝ,∀ n M : ℕ,4*(n:ℝ)*mesh ≤ 1 → L*(1+S)^3*mesh ≤ 1 →
      ∀ h : History w ell S start,∀ z : CostState,
        liveGood v mesh n h z → z ∈ arrivalSet v ell → ∀ c : ℝ,0 < c →
          PrimeExponentialTail.tailReward c (3*((M:ℝ)+1)) (some h) ≤
            ENNReal.ofReal 27*WeightedGapTail.tailReward (c/3) v ell M z := by
  obtain ⟨L,hL,hnear⟩ := nearby_inverse_ratio
  refine ⟨L,hL,?_⟩
  intro w ell S hell hS start hr hs hsS v mesh n M hclock hsmall h z hgood harr c hc
  have hrg : 0 < h.node.gap := terminal_gap_positive (by linarith) hr hs h.admissible
  have hqg : 0 < gapValue v z := Real.exp_pos _
  have hv : Valid h.node.side h.node.ratio := terminal_valid hs h.admissible
  have hnv : Valid h.node.side (stateRatio z.1) := by rw [hgood.2.1]; exact stateRatio_valid z.1
  have hsbound : h.node.ratio ≤ S := terminal_ratio_le hsS h.admissible
  have hweight := hnear S hS h.node.side h.node.ratio (stateRatio z.1) mesh hv hnv hsbound hgood.1 hgood.2.2.1 hsmall
  have hrel := NearbyParentGeometry.log_gap_relative hrg hqg (hgood.2.2.2.trans hclock)
  have hrq : h.node.gap ≤ 3*gapValue v z := hrel.1.trans
    (mul_le_mul_of_nonneg_right Real.exp_one_lt_three.le hqg.le)
  have hqr : gapValue v z ≤ 3*h.node.gap := hrel.2.trans
    (mul_le_mul_of_nonneg_right Real.exp_one_lt_three.le hrg.le)
  have hφ := weight_pos hv
  have hψ := weight_pos hnv
  have hreward := reward_factor_comparison hc hrg hqg hφ hψ hrq hqr hweight
  have hstate : weight h.node.side (stateRatio z.1) = stateWeight z.1 := by rw [hgood.2.1,stateWeight_eq]
  rw [hstate] at hreward
  by_cases hh : 3*((M:ℝ)+1) < h.node.gap
  · have hlow : (M:ℝ)+1 ≤ gapValue v z := by linarith
    have harrival : stateRatio z.1 < gapValue v z/ell := by
      rw [arrivalSet_eq_cutoff v (by linarith : 0 < ell)] at harr
      exact harr
    rw [PrimeExponentialTail.tailReward,ite_eq_left hh,WeightedGapTail.tailReward,
      indicator_of_mem (show z ∈ {z : CostState | (M:ℝ)+1 ≤ gapValue v z ∧ stateRatio z.1 < gapValue v z/ell} from ⟨hlow,harrival⟩)]
    rw [← div_eq_mul_inv,← ENNReal.ofReal_div_of_pos (stateWeight_pos z.1),
      ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 27)]
    exact ENNReal.ofReal_le_ofReal hreward
  · rw [PrimeExponentialTail.tailReward,ite_eq_right hh]
    exact zero_le

end NumberTheoryLean.SuccessfulRewardComparison

end

end Erdos970

end OAI
