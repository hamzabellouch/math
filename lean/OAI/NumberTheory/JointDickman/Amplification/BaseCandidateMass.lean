import OAI.NumberTheory.JointDickman.Amplification.FiniteRampMean
import OAI.NumberTheory.JointDickman.Amplification.ArithmeticPatternMeans
import OAI.NumberTheory.JointDickman.Amplification.CandidateExpectedDegree

namespace OAI

/-! # The mean candidate mass that controls the counting-cutoff error -/
namespace JointDickman
open Finset Filter Classical PublishedInputs
open scoped Topology

theorem baseCandidateContribution_sum (B L T H M u : ℕ) (τ C : ℝ) :
    (∑ e ∈ primeCandidatePool B M, baseCandidateContribution B L T H M τ C e u) =
      (∑ i, ∑ k, latentCandidateKernel B L T H M τ C
        (fun j => coefficientPrimeSet B (u+(j.val+1))) (smoothCandidateCutoff B T) i k)/2 := by
  let S := fun j : Fin M => coefficientPrimeSet B (u+(j.val+1))
  have hs : (∑ e ∈ primeCandidatePool B M, baseCandidateContribution B L T H M τ C e u) =
      ∑ e ∈ blockCandidates B L T H M τ C S,
        candidateMeanWeight B L τ C S (smoothCandidateCutoff B T) e := by
    symm
    calc
      _ = ∑ e ∈ blockCandidates B L T H M τ C S,
          baseCandidateContribution B L T H M τ C e u := by
        apply sum_congr rfl
        intro e he
        dsimp only [S] at he ⊢
        simp only [baseCandidateContribution,he,ite_true]
      _ = _ := by
        apply sum_subset (blockCandidates_subset_primePool (fun _ => filter_subset _ _))
        intro e _ he
        change e ∉ blockCandidates B L T H M τ C S at he
        dsimp only [S] at he
        simp only [baseCandidateContribution,he,ite_false]
  rw [hs]
  have ht := candidateMatrix_total
    (fun e : blockCandidates B L T H M τ C S => e.val.1.1)
    (fun e => e.val.1.2)
    (fun e => candidateMeanWeight B L τ C S (smoothCandidateCutoff B T) e.val)
  change (∑ e ∈ blockCandidates B L T H M τ C S,
    candidateMeanWeight B L τ C S (smoothCandidateCutoff B T) e) = _
  rw [sum_coe_sort (blockCandidates B L T H M τ C S)
    (fun e => candidateMeanWeight B L τ C S (smoothCandidateCutoff B T) e)] at ht
  change (∑ i, ∑ k, latentCandidateKernel B L T H M τ C S (smoothCandidateCutoff B T) i k) = _ at ht
  rw [ht]
  ring

theorem baseCandidateMassMean_eq (B L T H M : ℕ) (τ C : ℝ) :
    baseCandidateMassMean B L T H M τ C =
      arithmeticSquareMean B (fun u => (∑ i, ∑ k,
        latentCandidateKernel B L T H M τ C
          (fun j => coefficientPrimeSet B (u+(j.val+1))) (smoothCandidateCutoff B T) i k)/2) := by
  unfold baseCandidateMassMean
  rw [← sum_div,sum_comm]
  simp_rw [residueBaseContribution,baseCandidateContribution_sum]
  have hs := residue_sum_eq_range (q := auxiliarySquarePeriod B) (fun r =>
    (((∑ i, ∑ k, latentCandidateKernel B L T H M τ C
      (fun j => coefficientPrimeSet B (r.val+(j.val+1))) (smoothCandidateCutoff B T) i k)/2 : ℝ) : ℂ))
  have hs' : (∑ r : ZMod (auxiliarySquarePeriod B), (∑ i, ∑ k,
      latentCandidateKernel B L T H M τ C
        (fun j => coefficientPrimeSet B (r.val+(j.val+1))) (smoothCandidateCutoff B T) i k)/2) =
      ∑ u ∈ range (auxiliarySquarePeriod B), (∑ i, ∑ k,
      latentCandidateKernel B L T H M τ C
        (fun j => coefficientPrimeSet B (u+(j.val+1))) (smoothCandidateCutoff B T) i k)/2 := by
    simp only [ZMod.val_natCast] at hs
    have hp (u : ℕ) : (fun j : Fin M => coefficientPrimeSet B
        (u % auxiliarySquarePeriod B+(j.val+1))) =
        (fun j => coefficientPrimeSet B (u+(j.val+1))) :=
      blockPrimeSites_modEq (Nat.mod_modEq u _)
    simp only [hp] at hs
    exact_mod_cast hs
  rw [hs']
  simp only [arithmeticSquareMean,auxiliarySquarePeriod,Nat.cast_prod,Nat.cast_pow,← prod_pow]

theorem latentCandidateKernel_mean_total_le {B L T H M : ℕ} {τ C K : ℝ}
    (χ : BlockCandidateIndex M → ℝ)
    (hrow : ∀ (i : Fin M) (a : (auxiliaryPrimes B).powerset),
      (∑ k : Fin M, finiteExpectation (independentPrimeSetMass B)
        (fun R => candidateSiteKernel B L T H M τ C χ i k a.val R.val)) ≤ K) :
    finiteExpectation (siteProductMass (fun _ : Fin M => independentPrimeSetMass B))
      (fun S => ∑ i, ∑ k, latentCandidateKernel B L T H M τ C (fun j => (S j).val) χ i k) ≤
      (M : ℝ)*K := by
  let p := fun _ : Fin M => independentPrimeSetMass B
  have hp : ∀ i, ∑ a, p i a = 1 := fun _ => independentPrimeSetMass_sum B
  simp_rw [← latentPrimeSiteKernel_realizes,realizedSiteKernel]
  rw [finiteExpectation_sum]
  calc
    _ ≤ ∑ _i : Fin M, K := by
      apply sum_le_sum
      intro i _
      rw [finiteExpectation_sum]
      change (∑ k : Fin M, finiteExpectation (siteProductMass p)
        (fun S => latentPrimeSiteKernel B L T H M τ C χ i k (S i) (S k))) ≤ K
      have he (k : Fin M) : finiteExpectation (siteProductMass p)
          (fun S => latentPrimeSiteKernel B L T H M τ C χ i k (S i) (S k)) =
          finiteExpectation (p i) (fun a => finiteExpectation (p k)
            (fun b => latentPrimeSiteKernel B L T H M τ C χ i k a b)) := by
        by_cases hik : i = k
        · subst k
          simp only [latentPrimeSiteKernel,candidateSiteKernel_diag,finiteExpectation,mul_zero,sum_const_zero]
        · exact siteProduct_expectation_two p hp hik _
      simp_rw [he]
      rw [← finiteExpectation_sum]
      exact (finiteExpectation_mono (p i) (independentPrimeSetMass_nonneg B) (hrow i)).trans_eq
        (finiteExpectation_const (p i) (hp i) K)
    _ = _ := by simp

end JointDickman

end OAI
