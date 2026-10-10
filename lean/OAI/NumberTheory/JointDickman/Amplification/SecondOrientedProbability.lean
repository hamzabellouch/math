import OAI.NumberTheory.JointDickman.Amplification.OrientedProbabilityBound
import OAI.NumberTheory.JointDickman.Amplification.ConditionalOrientedEvent
import OAI.NumberTheory.JointDickman.Probability.ConditionalCoinSwap

namespace OAI

/-! # The second-recipient orientation, with the reciprocal ratio window -/

namespace JointDickman
open Finset

def secondOrientedTwoSplitTest (B L T : ℕ) (τ C Y : ℝ)
    (A R E D Q F : Finset ℕ) : Prop :=
  firstCoefficientGood B L T τ C A D ∧
  RegularPrimeSet B L τ C R ∧ RegularPrimeSet B L τ C Q ∧
  (∀ p ∈ symmDiff A E, Real.log p ≤ Y) ∧
  (∀ p ∈ symmDiff D F, Real.log p ≤ Y) ∧
  (∏ p ∈ E, p, ∏ p ∈ F, p) ∈ amplificationCoefficientPairs B T ∧
  ∃ p ∈ F \ D, Y / 2 < Real.log p

open Classical in
theorem secondOrientedTwoSplitTest_conditional_bound {B L T i : ℕ} {τ C : ℝ}
    {A D : Finset ℕ} (hB : 0 < B) (hT : 0 < T)
    (hA : A ⊆ auxiliaryPrimes B) (hD : D ⊆ auxiliaryPrimes B) :
    conditionalCoinAverage (auxiliaryPrimes B) A D (fun R Q I J U V =>
      if secondOrientedTwoSplitTest B L T τ C (primeTailEndpoint B i) A R (I ∪ U) D Q (J ∪ V)
      then 1 else 0) ≤
    if firstCoefficientGood B L T τ C A D then
      orientedSplitMass B D A (primeTailEndpoint B i) C (1 / (2 * T)) else 0 := by
  by_cases hg : firstCoefficientGood B L T τ C A D
  · rw [ite_eq_left hg, conditionalCoinAverage_swap]
    apply conditional_oriented_event_bound (L := L) (τ := τ) hD hA
    intro I _ J _ R _ Q _ U _ V _ _ _ he
    obtain ⟨_, hQreg, hRreg, hnA, hnD, hpair, hadd⟩ := he
    obtain ⟨_, _, hlo, hhi⟩ := (mem_amplificationCoefficientPairs hB).mp hpair
    have hlo' : (T : ℝ) * (∏ p ∈ I ∪ U, p : ℕ) ≤ (∏ p ∈ J ∪ V, p : ℕ) := by
      exact_mod_cast hlo
    have hhi' : (∏ p ∈ J ∪ V, p : ℕ) ≤ 2 * ((T : ℝ) * (∏ p ∈ I ∪ U, p : ℕ)) := by
      have hh : (∏ p ∈ J ∪ V, p : ℕ) < 2 * (T : ℝ) * (∏ p ∈ I ∪ U, p : ℕ) := by
        exact_mod_cast hhi
      nlinarith only [hh]
    have ht0 : (0 : ℝ) < T := by exact_mod_cast hT
    obtain ⟨hrlo, hrhi⟩ := reciprocal_ratio_bounds ht0 hlo' hhi'
    exact ⟨hRreg, hQreg, hnD, hnA, hrlo, hrhi, hadd⟩
  · have hf (R Q I J U V : Finset ℕ) :
        ¬ secondOrientedTwoSplitTest B L T τ C (primeTailEndpoint B i) A R (I ∪ U) D Q (J ∪ V) :=
      fun h => hg h.1
    simp only [conditionalCoinAverage, hg, hf, ite_false, mul_zero, sum_const_zero, le_refl]

open Classical in
/-- The second-recipient orientation probability is bounded by the first
coefficient average of the proved conditional operator. -/
theorem second_oriented_probability_bound {B L T i : ℕ} {τ C : ℝ} (hB : 0 < B) (hT : 0 < T) :
    twoSiteSplitProbability (auxiliaryPrimes B)
      (splitOrientationEvent (bothAmplificationSplitsGood B L T τ C) (primeTailEndpoint B i) true) ≤
    ∑ A ∈ (auxiliaryPrimes B).powerset, bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1 / 2 : ℝ) / p) A *
    ∑ D ∈ (auxiliaryPrimes B).powerset, bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1 / 2 : ℝ) / p) D *
      (if firstCoefficientGood B L T τ C A D then orientedSplitMass B D A (primeTailEndpoint B i) C (1 / (2 * T)) else 0) := by
  let F := fun A R E (_ : Finset ℕ) D Q H (_ : Finset ℕ) =>
    if secondOrientedTwoSplitTest B L T τ C (primeTailEndpoint B i) A R E D Q H then (1 : ℝ) else 0
  have hu : twoSiteSplitProbability (auxiliaryPrimes B)
      (splitOrientationEvent (bothAmplificationSplitsGood B L T τ C) (primeTailEndpoint B i) true) ≤
      ∑ x : TwoSiteSplit (auxiliaryPrimes B), twoSiteSplitMass (auxiliaryPrimes B) x *
        F x.first₁.val (x.site₁.val \ x.first₁.val) x.second₁.val (x.site₁.val \ x.second₁.val)
          x.first₂.val (x.site₂.val \ x.first₂.val) x.second₂.val (x.site₂.val \ x.second₂.val) := by
    apply sum_le_sum
    intro x _
    have hm := twoSiteSplitMass_nonneg (auxiliaryPrimes B) (auxiliaryPrimes_prime B) x
    by_cases he : splitOrientationEvent (bothAmplificationSplitsGood B L T τ C) (primeTailEndpoint B i) true x
    · have ht : secondOrientedTwoSplitTest B L T τ C (primeTailEndpoint B i)
          x.first₁.val (x.site₁.val \ x.first₁.val) x.second₁.val
          x.first₂.val (x.site₂.val \ x.first₂.val) x.second₂.val := by
        refine ⟨⟨he.1.1.1, he.1.1.2.1, he.1.1.2.2.1⟩,
          he.1.1.2.2.2.1, he.1.1.2.2.2.2, ?_, ?_, he.1.2.1, he.2.2⟩
        · intro p hp
          exact he.2.1 p (mem_union_left _ hp)
        · intro p hp
          exact he.2.1 p (mem_union_right _ hp)
      simp only [he, F, ht, ite_true, mul_one, le_refl]
    · simp only [he, ite_false, F]
      split_ifs <;> simp only [mul_one, mul_zero]
      · exact hm
      · exact le_rfl
  apply hu.trans
  rw [twoSiteSplit_coin_law (auxiliaryPrimes B) (auxiliaryPrimes_prime B)]
  apply sum_le_sum
  intro A hA
  apply mul_le_mul_of_nonneg_left
  · apply sum_le_sum
    intro D hD
    exact mul_le_mul_of_nonneg_left
      (secondOrientedTwoSplitTest_conditional_bound hB hT (mem_powerset.mp hA) (mem_powerset.mp hD))
      (bernoulliSubsetMass_nonneg (mem_powerset.mp hD) (fun p hp => by
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (auxiliaryPrimes_prime B p hp).two_le
        exact ⟨by positivity, (div_le_one (by linarith)).mpr (by linarith)⟩))
  · apply bernoulliSubsetMass_nonneg (mem_powerset.mp hA)
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (auxiliaryPrimes_prime B p hp).two_le
    exact ⟨by positivity, (div_le_one (by linarith)).mpr (by linarith)⟩

end JointDickman

end OAI
