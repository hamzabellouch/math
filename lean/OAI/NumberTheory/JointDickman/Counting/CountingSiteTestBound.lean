import OAI.NumberTheory.JointDickman.Counting.CountingSiteTest

namespace OAI

/-! # The normalized pair comparison gives the full block test estimate -/
namespace JointDickman
open Finset Classical PublishedInputs

theorem countingSiteError_pair_bound
    (P : MvPolynomial (Fin 4) ℝ) (m : (Fin 4 →₀ ℕ) → ℕ)
    (B L T H M : ℕ) (τ C w : ℝ) (c : (Fin 4 →₀ ℕ) → ℕ → ℝ)
    (D : (Fin 4 →₀ ℕ) → ℕ) (σ r : ℝ) (hT : 0 < T) (hr : 0 ≤ r)
    (happrox : ∀ i k : Fin M, i < k → H < k.val-i.val → k.val-i.val < T →
      ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
      (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
      (T : ℝ)*|subsetKernelBilinear B (subsetSiteTest (auxiliaryPrimes B) g)
          (subsetSiteTest (auxiliaryPrimes B) h)
          (candidateSiteKernel B L T H M τ C (rampedCandidateCutoff B T w σ) i k)-
        subsetKernelBilinear B (subsetSiteTest (auxiliaryPrimes B) g)
          (subsetSiteTest (auxiliaryPrimes B) h)
          (countingCandidateModel P m B L (k.val-i.val) τ C c D T σ)| ≤
        r*singularFactor 24 (k.val-i.val))
    (i k : Fin M) (g h : (auxiliaryPrimes B).powerset → ℝ)
    (hg : ∀ a, |g a| ≤ 1) (hh : ∀ b, |h b| ≤ 1) :
    |finiteExpectation (independentPrimeSetMass B) (fun a =>
      finiteExpectation (independentPrimeSetMass B) (fun b =>
        countingSiteError P m B L T H M τ C w c D σ i k a b*g a*h b))| ≤ lagEnvelope T r i k := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hf (i k : Fin M) (hik : i < k) (g h : (auxiliaryPrimes B).powerset → ℝ)
      (hg : ∀ a, |g a| ≤ 1) (hh : ∀ b, |h b| ≤ 1) :
      |finiteExpectation (independentPrimeSetMass B) (fun a =>
        finiteExpectation (independentPrimeSetMass B) (fun b =>
          countingSiteError P m B L T H M τ C w c D σ i k a b*g a*h b))| ≤ lagEnvelope T r i k := by
    by_cases ha : H < k.val-i.val ∧ k.val-i.val < T
    · have hp := subset_pair_error_of_boolean_tests B
        (candidateSiteKernel B L T H M τ C (rampedCandidateCutoff B T w σ) i k)
        (countingCandidateModel P m B L (k.val-i.val) τ C c D T σ)
        (fun g h hg hh => (le_div_iff₀ hTr).mpr (by
          simpa only [mul_comm] using happrox i k hik ha.1 ha.2 g h hg hh)) g h hg hh
      have he : lagEnvelope T r i k = (r*singularFactor 24 (k.val-i.val))/(T : ℝ) := by
        rw [lagEnvelope,ite_eq_left ⟨ne_of_lt hik,by simpa [Nat.dist_eq_sub_of_le hik.le] using ha.2⟩,
          Nat.dist_eq_sub_of_le hik.le]
        ring
      rw [he]
      simpa only [countingSiteError,latentPrimeSiteKernel,countingSiteModel,hik,ite_true,ha,and_self] using hp
    · have hz (a b : (auxiliaryPrimes B).powerset) :
          countingSiteError P m B L T H M τ C w c D σ i k a b = 0 := by
        have hzero : candidateSiteKernel B L T H M τ C (rampedCandidateCutoff B T w σ) i k a.val b.val = 0 := by
          by_cases hs : k.val-i.val ≤ H
          · exact candidateSiteKernel_zero_of_short _ i k _ _ (by
              simpa only [Nat.dist_eq_sub_of_le hik.le] using hs)
          · have hfar : T ≤ k.val-i.val := by omega
            exact candidateSiteKernel_zero_of_far _ i k _ _ (by
              simpa only [Nat.dist_eq_sub_of_le hik.le] using hfar)
        simp only [countingSiteError,latentPrimeSiteKernel,hzero,countingSiteModel,hik,ite_true,ha,ite_false,sub_self]
      simp only [hz,zero_mul,finiteExpectation,mul_zero,sum_const_zero,abs_zero]
      exact lagEnvelope_nonneg T hr i k
  rcases lt_trichotomy i k with hik | rfl | hki
  · exact hf i k hik g h hg hh
  · simp only [countingSiteError,latentPrimeSiteKernel,candidateSiteKernel_diag,countingSiteModel_diag,
      sub_self,zero_mul,finiteExpectation,mul_zero,sum_const_zero,abs_zero,lagEnvelope,
      ne_eq,not_true_eq_false,false_and,ite_false,le_refl]
  · have he : finiteExpectation (independentPrimeSetMass B) (fun a =>
        finiteExpectation (independentPrimeSetMass B) (fun b =>
          countingSiteError P m B L T H M τ C w c D σ i k a b*g a*h b)) =
        finiteExpectation (independentPrimeSetMass B) (fun b =>
          finiteExpectation (independentPrimeSetMass B) (fun a =>
            countingSiteError P m B L T H M τ C w c D σ k i b a*h b*g a)) := by
      rw [finiteExpectation_swap]
      apply congrArg (finiteExpectation (independentPrimeSetMass B))
      funext b
      apply congrArg (finiteExpectation (independentPrimeSetMass B))
      funext a
      rw [countingSiteError_symm]
      ring
    rw [he]
    simpa only [lagEnvelope,Nat.dist_comm,ne_comm] using hf k i hki h g hh hg

end JointDickman

end OAI
