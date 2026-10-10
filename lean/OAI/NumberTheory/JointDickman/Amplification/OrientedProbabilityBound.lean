import OAI.NumberTheory.JointDickman.Amplification.NativeOrientedEvent
import OAI.NumberTheory.JointDickman.Probability.ConditionalCoinSupport
import OAI.NumberTheory.JointDickman.Probability.TwoSiteCoinLaw
import OAI.NumberTheory.JointDickman.Probability.SplitOrientationCover

namespace OAI

/-! # Applying the oriented conditional bound to the actual two-site event -/

namespace JointDickman
open Finset

def firstCoefficientGood (B L T : ℕ) (τ C : ℝ) (A D : Finset ℕ) : Prop :=
  (∏ p ∈ A, p, ∏ p ∈ D, p) ∈ amplificationCoefficientPairs B T ∧
  RegularPrimeSet B L τ C A ∧ RegularPrimeSet B L τ C D

def orientedTwoSplitTest (B L T : ℕ) (τ C Y : ℝ)
    (A R E D Q F : Finset ℕ) : Prop :=
  firstCoefficientGood B L T τ C A D ∧
  RegularPrimeSet B L τ C R ∧ RegularPrimeSet B L τ C Q ∧
  (∀ p ∈ symmDiff A E, Real.log p ≤ Y) ∧
  (∀ p ∈ symmDiff D F, Real.log p ≤ Y) ∧
  (∏ p ∈ E, p, ∏ p ∈ F, p) ∈ amplificationCoefficientPairs B T ∧
  ∃ p ∈ E \ A, Y / 2 < Real.log p

open Classical in
theorem orientedTwoSplitTest_conditional_bound {B L T i : ℕ} {τ C : ℝ}
    {A D : Finset ℕ} (hB : 0 < B)
    (hA : A ⊆ auxiliaryPrimes B) (hD : D ⊆ auxiliaryPrimes B) :
    conditionalCoinAverage (auxiliaryPrimes B) A D (fun R Q I J U V =>
      if orientedTwoSplitTest B L T τ C (primeTailEndpoint B i) A R (I ∪ U) D Q (J ∪ V)
      then 1 else 0) ≤
    if firstCoefficientGood B L T τ C A D then
      orientedSplitMass B A D (primeTailEndpoint B i) C T else 0 := by
  by_cases hg : firstCoefficientGood B L T τ C A D
  · rw [ite_eq_left hg]
    apply le_trans (b := nativeOrientedMass B L T τ C (primeTailEndpoint B i) A D)
      ?_ (nativeOrientedMass_le hB hA hD)
    unfold nativeOrientedMass
    apply conditionalCoinAverage_le_on_support (auxiliaryPrimes_prime B)
    intro I _ J _ R _ Q _ U hU V hV hAR hDQ
    by_cases he : orientedTwoSplitTest B L T τ C (primeTailEndpoint B i) A R (I ∪ U) D Q (J ∪ V)
    · have hn : nativeOrientedEvent B L T τ C (primeTailEndpoint B i) A D R Q I J U V :=
        ⟨hAR, hDQ, hU, hV, he.2.1, he.2.2.1, he.2.2.2.1,
          he.2.2.2.2.1, he.2.2.2.2.2.1, he.2.2.2.2.2.2⟩
      simp only [he, hn, ite_true, le_refl]
    · simp only [he, ite_false]
      split_ifs <;> norm_num
  · have hf (R Q I J U V : Finset ℕ) :
        ¬ orientedTwoSplitTest B L T τ C (primeTailEndpoint B i) A R (I ∪ U) D Q (J ∪ V) :=
      fun h => hg h.1
    simp only [conditionalCoinAverage, hg, hf, ite_false, mul_zero, sum_const_zero, le_refl]

open Classical in
/-- The first-recipient orientation probability is bounded by the first
coefficient average of the proved conditional operator. -/
theorem oriented_probability_bound {B L T i : ℕ} {τ C : ℝ} (hB : 0 < B) :
    twoSiteSplitProbability (auxiliaryPrimes B)
      (splitOrientationEvent (bothAmplificationSplitsGood B L T τ C) (primeTailEndpoint B i) false) ≤
    ∑ A ∈ (auxiliaryPrimes B).powerset, bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1 / 2 : ℝ) / p) A *
    ∑ D ∈ (auxiliaryPrimes B).powerset, bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1 / 2 : ℝ) / p) D *
      (if firstCoefficientGood B L T τ C A D then orientedSplitMass B A D (primeTailEndpoint B i) C T else 0) := by
  let F := fun A R E (_ : Finset ℕ) D Q H (_ : Finset ℕ) =>
    if orientedTwoSplitTest B L T τ C (primeTailEndpoint B i) A R E D Q H then (1 : ℝ) else 0
  have hu : twoSiteSplitProbability (auxiliaryPrimes B)
      (splitOrientationEvent (bothAmplificationSplitsGood B L T τ C) (primeTailEndpoint B i) false) ≤
      ∑ x : TwoSiteSplit (auxiliaryPrimes B), twoSiteSplitMass (auxiliaryPrimes B) x *
        F x.first₁.val (x.site₁.val \ x.first₁.val) x.second₁.val (x.site₁.val \ x.second₁.val)
          x.first₂.val (x.site₂.val \ x.first₂.val) x.second₂.val (x.site₂.val \ x.second₂.val) := by
    apply sum_le_sum
    intro x _
    have hm := twoSiteSplitMass_nonneg (auxiliaryPrimes B) (auxiliaryPrimes_prime B) x
    by_cases he : splitOrientationEvent (bothAmplificationSplitsGood B L T τ C) (primeTailEndpoint B i) false x
    · have ht : orientedTwoSplitTest B L T τ C (primeTailEndpoint B i)
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
      (orientedTwoSplitTest_conditional_bound hB (mem_powerset.mp hA) (mem_powerset.mp hD))
      (bernoulliSubsetMass_nonneg (mem_powerset.mp hD) (fun p hp => by
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (auxiliaryPrimes_prime B p hp).two_le
        exact ⟨by positivity, (div_le_one (by linarith)).mpr (by linarith)⟩))
  · apply bernoulliSubsetMass_nonneg (mem_powerset.mp hA)
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (auxiliaryPrimes_prime B p hp).two_le
    exact ⟨by positivity, (div_le_one (by linarith)).mpr (by linarith)⟩

end JointDickman

end OAI
