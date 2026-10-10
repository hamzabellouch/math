import OAI.NumberTheory.JointDickman.Probability.NoChangeCoinOperator
import OAI.NumberTheory.JointDickman.Amplification.OrientedProbabilityBound

namespace OAI

/-! # The no-change event in the exact conditional law -/

namespace JointDickman
open Finset

theorem unchanged_split_parts {A R I U : Finset ℕ} (hd : Disjoint A R)
    (hU : U ⊆ R) (he : I ∪ U = A) : I = A ∧ U = ∅ := by
  have huA : U ⊆ A := by rw [← he]; exact subset_union_right
  have hu : U = ∅ := eq_empty_iff_forall_notMem.mpr (fun p hp =>
    disjoint_left.mp hd (huA hp) (hU hp))
  exact ⟨by simpa only [hu, union_empty] using he, hu⟩

theorem regular_card_at_cutoff {B L : ℕ} {τ C : ℝ} {R : Finset ℕ}
    (hB : 1 < B) (hR : R ⊆ auxiliaryPrimes B) (hr : RegularPrimeSet B L τ C R) :
    (2 / 5 : ℝ) * Real.log ((B : ℝ) / Real.log (auxiliaryCutoff B)) - C ≤ (R.card : ℝ) := by
  have hh := hr.2 0
  simp only [primeTailEndpoint, pow_zero, one_mul] at hh
  change _ ≤ ((highPrimePart (Real.log (auxiliaryCutoff B)) R).card : ℝ) at hh
  rwa [highPrimePart_at_cutoff hB hR] at hh

def noChangeTwoSplitTest (B L T : ℕ) (τ C : ℝ) (A R E D Q F : Finset ℕ) : Prop :=
  firstCoefficientGood B L T τ C A D ∧ RegularPrimeSet B L τ C R ∧
    RegularPrimeSet B L τ C Q ∧ E = A ∧ F = D

open Classical in
theorem noChangeTwoSplitTest_conditional_bound {B L T : ℕ} {τ C : ℝ}
    {A D : Finset ℕ} (hB : 1 < B)
    :
    conditionalCoinAverage (auxiliaryPrimes B) A D (fun R Q I J U V =>
      if noChangeTwoSplitTest B L T τ C A R (I ∪ U) D Q (J ∪ V) then 1 else 0) ≤
    if firstCoefficientGood B L T τ C A D then noChangeSplitMass B A D C else 0 := by
  by_cases hg : firstCoefficientGood B L T τ C A D
  · rw [ite_eq_left hg]
    let k := (2 / 5 : ℝ) * Real.log ((B : ℝ) / Real.log (auxiliaryCutoff B)) - C
    have hn : noChangeSplitMass B A D C = noChangeCoinOperator (auxiliaryPrimes B) A D k :=
      (noChangeCoinOperator_eq _ _ _ _).symm
    rw [hn, noChangeCoinOperator_expansion]
    apply conditionalCoinAverage_le_on_support (auxiliaryPrimes_prime B)
    intro I _ J _ R hR Q hQ U hU V hV hAR hDQ
    by_cases he : noChangeTwoSplitTest B L T τ C A R (I ∪ U) D Q (J ∪ V)
    · obtain ⟨hi, hu⟩ := unchanged_split_parts hAR hU he.2.2.2.1
      obtain ⟨hj, hv⟩ := unchanged_split_parts hDQ hV he.2.2.2.2
      have hr := regular_card_at_cutoff hB hR he.2.1
      have hq := regular_card_at_cutoff hB hQ he.2.2.1
      rw [ite_eq_left he]
      change k ≤ (R.card : ℝ) at hr
      change k ≤ (Q.card : ℝ) at hq
      simp only [hi, hj, hu, hv, hr, hq, and_self, ite_true, le_refl]
    · simp only [he, ite_false]
      split_ifs <;> norm_num
  · have hf (R Q I J U V : Finset ℕ) :
        ¬ noChangeTwoSplitTest B L T τ C A R (I ∪ U) D Q (J ∪ V) := fun h => hg h.1
    simp only [conditionalCoinAverage, hg, hf, ite_false, mul_zero, sum_const_zero, le_refl]

end JointDickman

end OAI
