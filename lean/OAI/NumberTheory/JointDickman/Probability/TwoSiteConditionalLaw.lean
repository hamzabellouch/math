import OAI.NumberTheory.JointDickman.Probability.TwoSiteSplitSums

namespace OAI

/-! # The coefficient-first law of two sites and their second splits -/

namespace JointDickman

open Finset

/-- The exact joint law, with both first remaining sets sampled from their
proved conditional parameters. No independence replacement or coupling occurs. -/
theorem twoSiteSplit_conditional (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (F : Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ →
      Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → ℝ) :
    (∑ x : TwoSiteSplit P, twoSiteSplitMass P x *
      F x.first₁.val (x.site₁.val \ x.first₁.val) x.second₁.val (x.site₁.val \ x.second₁.val)
        x.first₂.val (x.site₂.val \ x.first₂.val) x.second₂.val (x.site₂.val \ x.second₂.val)) =
      ∑ A ∈ P.powerset, bernoulliSubsetMass P (fun p => (1 / 2 : ℝ) / p) A *
      ∑ R ∈ P.powerset, bernoulliSubsetMass P (remainingPrimeParameter A) R *
      ∑ I ∈ A.powerset, ∑ U ∈ R.powerset, subsetRetentionMass A I * subsetRetentionMass R U *
      (∑ D ∈ P.powerset, bernoulliSubsetMass P (fun p => (1 / 2 : ℝ) / p) D *
      ∑ Q ∈ P.powerset, bernoulliSubsetMass P (remainingPrimeParameter D) Q *
      ∑ J ∈ D.powerset, ∑ V ∈ Q.powerset, subsetRetentionMass D J * subsetRetentionMass Q V *
        F A R (I ∪ U) ((A \ I) ∪ (R \ U)) D Q (J ∪ V) ((D \ J) ∪ (Q \ V))) := by
  rw [twoSiteSplit_expectation]
  rw [twoSplitSiteAverage_conditional P hP]
  simp_rw [twoSplitSiteAverage_conditional P hP]

end JointDickman

end OAI
