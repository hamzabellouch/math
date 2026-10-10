import OAI.NumberTheory.JointDickman.Probability.SitePartition
import OAI.NumberTheory.JointDickman.Probability.CandidateThirdSiteProbability

namespace OAI

/-! # Integrating a bound conditional on exposed sites -/

namespace JointDickman
open Finset PublishedInputs

open Classical in
theorem siteProduct_probability_of_conditional_bound
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]
    (p : ι → Ω → ℝ) (hp : ∀ i x, 0 ≤ p i x)
    (hpone : ∀ i, ∑ x, p i x = 1) (I : Finset ι)
    (E : (ι → Ω) → Prop) {K : ℝ}
    (hK : ∀ a : I → Ω,
      finiteProbability (siteProductMass (fun i : {i : ι // i ∉ I} => p i.val))
        (fun b => E (mergeSitePartition I a b)) ≤ K) :
    finiteProbability (siteProductMass p) E ≤ K := by
  rw [finiteProbability_eq_indicator_mean, siteProduct_partition p I]
  calc
    _ ≤ finiteExpectation (siteProductMass (fun i : I => p i.val)) (fun _ => K) := by
      apply finiteExpectation_mono _
        (siteProductMass_nonneg (fun i : I => p i.val) (fun i => hp i.val))
      intro a
      simpa only [← finiteProbability_eq_indicator_mean] using hK a
    _ = K := finiteExpectation_const _
      (siteProductMass_sum (fun i : I => p i.val) (fun i => hpone i.val)) K

end JointDickman

end OAI
