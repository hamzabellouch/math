import OAI.NumberTheory.JointDickman.Amplification.NoChangeConditional
import OAI.NumberTheory.JointDickman.Counting.FirstCoefficientAverage

namespace OAI

/-! # Integrating the actual no-change event over its first coefficients -/

namespace JointDickman
open Finset

open Classical in
theorem no_change_probability_bound {B L T : ℕ} {τ C : ℝ} (hB : 1 < B) :
    twoSiteSplitProbability (auxiliaryPrimes B)
      (fun x => bothAmplificationSplitsGood B L T τ C x ∧ twoSiteNoChange x) ≤
    firstCoefficientAverage B L T τ C (fun A D => noChangeSplitMass B A D C) := by
  let F := fun A R E (_ : Finset ℕ) D Q H (_ : Finset ℕ) =>
    if noChangeTwoSplitTest B L T τ C A R E D Q H then (1 : ℝ) else 0
  have hu : twoSiteSplitProbability (auxiliaryPrimes B)
      (fun x => bothAmplificationSplitsGood B L T τ C x ∧ twoSiteNoChange x) ≤
      ∑ x : TwoSiteSplit (auxiliaryPrimes B), twoSiteSplitMass (auxiliaryPrimes B) x *
        F x.first₁.val (x.site₁.val \ x.first₁.val) x.second₁.val (x.site₁.val \ x.second₁.val)
          x.first₂.val (x.site₂.val \ x.first₂.val) x.second₂.val (x.site₂.val \ x.second₂.val) := by
    apply sum_le_sum
    intro x _
    have hm := twoSiteSplitMass_nonneg (auxiliaryPrimes B) (auxiliaryPrimes_prime B) x
    by_cases he : bothAmplificationSplitsGood B L T τ C x ∧ twoSiteNoChange x
    · have ht : noChangeTwoSplitTest B L T τ C
          x.first₁.val (x.site₁.val \ x.first₁.val) x.second₁.val
          x.first₂.val (x.site₂.val \ x.first₂.val) x.second₂.val :=
        ⟨⟨he.1.1.1, he.1.1.2.1, he.1.1.2.2.1⟩,
          he.1.1.2.2.2.1, he.1.1.2.2.2.2,
          congrArg Subtype.val he.2.1.symm, congrArg Subtype.val he.2.2.symm⟩
      simp only [he, F, ht, and_self, ite_true, mul_one, le_refl]
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
      (noChangeTwoSplitTest_conditional_bound hB)
      (auxiliaryHalfSubsetMass_nonneg (mem_powerset.mp hD))
  · exact auxiliaryHalfSubsetMass_nonneg (mem_powerset.mp hA)

end JointDickman

end OAI
