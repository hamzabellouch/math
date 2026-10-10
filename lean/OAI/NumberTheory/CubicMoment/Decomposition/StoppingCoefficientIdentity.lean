import OAI.NumberTheory.CubicMoment.Estimates.PrimeStoppingCollection
import OAI.NumberTheory.CubicMoment.Estimates.PrimeFactorPairs

namespace OAI

/-! The literal fixed-label stopping contribution as a sum over primary
factor pairs. This is the arithmetic bridge to independent alpha/beta. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

/-- Exact fixed-label coefficient identity, before any estimate or
extension by vanishing nonsquarefree terms. -/
theorem stopping_primary_pair_sum {n : Eisenstein} (hn : primary n)
    (hs : Squarefree n) {B : ℝ} (hnB : norm n ≤ B)
    (bin : Eisenstein → ℕ) (ell : ℕ → ℝ) (j k l : ℕ) (Z : ℝ) (r : Eisenstein)
    (ψ : ℝ → ℝ) (w : ℝ) (K : Eisenstein → Eisenstein → ℂ) :
    (∑ t ∈ (primeBin (primaryPrimeFactors n) bin j).powersetCard k,
      if (primeBin (stoppingRemainder (primaryPrimeFactors n) bin j t) bin j).card = l ∧
          (norm r*primeSurrogate (stoppingSelected (primaryPrimeFactors n) bin j t) bin ell/
              ell j < Z ∧
            Z ≤ norm r*primeSurrogate
              (stoppingSelected (primaryPrimeFactors n) bin j t) bin ell) then
        cutoffMoebius ψ w (∏ p ∈ stoppingSelected (primaryPrimeFactors n) bin j t, p)*
          cutoffMoebius ψ w (∏ p ∈ stoppingRemainder (primaryPrimeFactors n) bin j t, p)*
          K (∏ p ∈ stoppingSelected (primaryPrimeFactors n) bin j t, p)
            (∏ p ∈ stoppingRemainder (primaryPrimeFactors n) bin j t, p)
      else 0) =
    ∑ q ∈ ((primaryElementBall B).product (primaryElementBall B)).filter
        (fun q => q.1*q.2 = n),
      if stoppingSideTest bin ell j k Z r q.1 ∧ stoppingRemainingTest bin j l q.2 then
        cutoffMoebius ψ w q.1*cutoffMoebius ψ w q.2*K q.1 q.2 else 0 := by
  rw [←squarefree_primary_factor_pairs hn hs hnB
    (fun d e => if stoppingSideTest bin ell j k Z r d ∧ stoppingRemainingTest bin j l e then
      cutoffMoebius ψ w d*cutoffMoebius ψ w e*K d e else 0)]
  let F := fun d e : Finset Eisenstein =>
    if (primeBin e bin j).card = l ∧
        (norm r*primeSurrogate d bin ell/ell j < Z ∧
          Z ≤ norm r*primeSurrogate d bin ell) then
      cutoffMoebius ψ w (∏ p ∈ d, p)*cutoffMoebius ψ w (∏ p ∈ e, p)*
        K (∏ p ∈ d, p) (∏ p ∈ e, p) else 0
  change (∑ t ∈ (primeBin (primaryPrimeFactors n) bin j).powersetCard k,
    F (stoppingSelected (primaryPrimeFactors n) bin j t)
      (stoppingRemainder (primaryPrimeFactors n) bin j t)) = _
  rw [stopping_subset_sum]
  unfold stoppingDivisorSubsets
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  have hsub := Finset.mem_powerset.mp hd
  have hdp : ∀ p ∈ d, primaryPrime p :=
    fun p hp => (primaryPrimeFactor_spec hn (hsub hp)).1
  have hep : ∀ p ∈ primaryPrimeFactors n \ d, primaryPrime p :=
    fun p hp => (primaryPrimeFactor_spec hn (Finset.mem_sdiff.mp hp).1).1
  dsimp only [F]
  unfold stoppingSideTest stoppingPrimeSetTest stoppingRemainingTest
  rw [primaryPrimeFactors_finset_prod d hdp,
    primaryPrimeFactors_finset_prod (primaryPrimeFactors n \ d) hep]
  rw [←ite_and]
  split_ifs <;> first | rfl | (exfalso; tauto)

/-- Summing the fixed-label identity over the original squarefree terms
leaves the sharp product cutoff on the independent factor pair. -/
theorem stopping_primary_cutoff_sum (B : ℝ)
    (bin : Eisenstein → ℕ) (ell : ℕ → ℝ) (j k l : ℕ) (Z : ℝ) (r : Eisenstein)
    (ψ : ℝ → ℝ) (w : ℝ) (K : Eisenstein → Eisenstein → ℂ) :
    (∑ n ∈ (primaryElementBall B).filter Squarefree,
      ∑ t ∈ (primeBin (primaryPrimeFactors n) bin j).powersetCard k,
        if (primeBin (stoppingRemainder (primaryPrimeFactors n) bin j t) bin j).card = l ∧
            (norm r*primeSurrogate (stoppingSelected (primaryPrimeFactors n) bin j t) bin ell/
                ell j < Z ∧
              Z ≤ norm r*primeSurrogate
                (stoppingSelected (primaryPrimeFactors n) bin j t) bin ell) then
          cutoffMoebius ψ w (∏ p ∈ stoppingSelected (primaryPrimeFactors n) bin j t, p)*
            cutoffMoebius ψ w (∏ p ∈ stoppingRemainder (primaryPrimeFactors n) bin j t, p)*
            K (∏ p ∈ stoppingSelected (primaryPrimeFactors n) bin j t, p)
              (∏ p ∈ stoppingRemainder (primaryPrimeFactors n) bin j t, p)
        else 0) =
    ∑ d ∈ primaryElementBall B, ∑ e ∈ primaryElementBall B,
      if Squarefree (d*e) ∧ norm (d*e) ≤ B then
        (if stoppingSideTest bin ell j k Z r d ∧ stoppingRemainingTest bin j l e then
          cutoffMoebius ψ w d*cutoffMoebius ψ w e*K d e else 0)
      else 0 := by
  let F := fun d e : Eisenstein =>
    if stoppingSideTest bin ell j k Z r d ∧ stoppingRemainingTest bin j l e then
      cutoffMoebius ψ w d*cutoffMoebius ψ w e*K d e else 0
  calc
    _ = ∑ n ∈ (primaryElementBall B).filter Squarefree,
        ∑ s ∈ (primaryPrimeFactors n).powerset,
          F (∏ p ∈ s, p) (∏ p ∈ primaryPrimeFactors n \ s, p) := by
      apply Finset.sum_congr rfl
      intro n hn
      obtain ⟨hnB,hs⟩ := Finset.mem_filter.mp hn
      obtain ⟨hprim,hnorm⟩ := mem_primaryElementBall.mp hnB
      rw [stopping_primary_pair_sum hprim hs hnorm]
      exact (squarefree_primary_factor_pairs hprim hs hnorm F).symm
    _ = _ := squarefree_primary_subset_cutoff_sum B F

/-- A squarefree-supported kernel removes the coupled squarefree test,
but does not remove the literal product cutoff. -/
theorem stopping_primary_cutoff_sum_vanishing (B : ℝ)
    (bin : Eisenstein → ℕ) (ell : ℕ → ℝ) (j k l : ℕ) (Z : ℝ) (r : Eisenstein)
    (ψ : ℝ → ℝ) (w : ℝ) (K : Eisenstein → Eisenstein → ℂ)
    (hK : ∀ d ∈ primaryElementBall B, ∀ e ∈ primaryElementBall B,
      ¬Squarefree (d*e) → K d e = 0) :
    (∑ n ∈ (primaryElementBall B).filter Squarefree,
      ∑ t ∈ (primeBin (primaryPrimeFactors n) bin j).powersetCard k,
        if (primeBin (stoppingRemainder (primaryPrimeFactors n) bin j t) bin j).card = l ∧
            (norm r*primeSurrogate (stoppingSelected (primaryPrimeFactors n) bin j t) bin ell/
                ell j < Z ∧
              Z ≤ norm r*primeSurrogate
                (stoppingSelected (primaryPrimeFactors n) bin j t) bin ell) then
          cutoffMoebius ψ w (∏ p ∈ stoppingSelected (primaryPrimeFactors n) bin j t, p)*
            cutoffMoebius ψ w (∏ p ∈ stoppingRemainder (primaryPrimeFactors n) bin j t, p)*
            K (∏ p ∈ stoppingSelected (primaryPrimeFactors n) bin j t, p)
              (∏ p ∈ stoppingRemainder (primaryPrimeFactors n) bin j t, p)
        else 0) =
    ∑ d ∈ primaryElementBall B, ∑ e ∈ primaryElementBall B,
      if norm (d*e) ≤ B ∧ stoppingSideTest bin ell j k Z r d ∧
          stoppingRemainingTest bin j l e then
        cutoffMoebius ψ w d*cutoffMoebius ψ w e*K d e else 0 := by
  rw [stopping_primary_cutoff_sum]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  by_cases hs : Squarefree (d*e)
  · by_cases hn : norm (d*e) ≤ B <;>
      simp only [hs,hn,true_and,false_and,ite_true,ite_false]
  · simp [hs,hK d hd e he hs]

end CubicFirstMoment

end

end OAI
