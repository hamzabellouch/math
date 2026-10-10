import OAI.NumberTheory.JointDickman.Arithmetic.CandidateGoodPrimes
import OAI.NumberTheory.JointDickman.Amplification.RestrictedRootComparison

namespace OAI

/-! # Conditional candidate-root distribution at an unoccupied prime -/

namespace JointDickman
open Finset

noncomputable def outsideCandidatePrimeMass {M : ℕ} (I : Finset (BlockCandidateIndex M))
    (p : ℕ) [Fact p.Prime] (S : I.powerset) : ℝ :=
  restrictedRootMass I (candidateModRoot p) (univ \ univ.image (blockSiteRoot M p)) S

theorem blockForbidden_card {M p : ℕ} (hp : M < p) :
    (univ.image (blockSiteRoot M p)).card = M := by
  classical
  rw [card_image_of_injective _ (blockSiteRoot_injective M p hp),card_univ,Fintype.card_fin]

theorem outsideCandidatePrimeMass_nonneg {M : ℕ} (I : Finset (BlockCandidateIndex M))
    (p : ℕ) [Fact p.Prime] (S : I.powerset) : 0 ≤ outsideCandidatePrimeMass I p S :=
  restrictedRootMass_nonneg _ _ _ _

theorem outsideCandidatePrimeMass_sum {M : ℕ} (I : Finset (BlockCandidateIndex M))
    (p : ℕ) [Fact p.Prime] (hp : M < p) : (∑ S, outsideCandidatePrimeMass I p S) = 1 := by
  apply restrictedRootMass_sum
  rw [card_sdiff_of_subset (subset_univ _),card_univ,ZMod.card,blockForbidden_card hp]
  omega

open Classical in
theorem outsideCandidatePrimeMass_l1 {B M p : ℕ} [Fact p.Prime]
    (I : Finset (BlockCandidateIndex M)) (hp : p ∈ auxiliaryPrimes B)
    (hsize : M < p) (hhalf : 2*M ≤ p) :
    (∑ S : I.powerset, |outsideCandidatePrimeMass I p S-
      bernoulliSubsetMass I (fun _ => 1/(p : ℝ)) S.val|) ≤
      8*((I.card : ℝ)+(M : ℝ))^2/(p : ℝ)^2+
        if p ∈ candidateDefectPrimes B I then 6*(I.card : ℝ)/(p : ℝ) else 0 := by
  have hcard := blockForbidden_card hsize
  by_cases hbad : p ∈ candidateDefectPrimes B I
  · rw [ite_eq_left hbad]
    have hU : 0 < (univ \ univ.image (blockSiteRoot M p)).card := by
      rw [card_sdiff_of_subset (subset_univ _),card_univ,ZMod.card,hcard]
      omega
    have hh := restrictedRootMass_l1_crude I (Fact.out : p.Prime) (candidateModRoot p)
      (univ \ univ.image (blockSiteRoot M p)) hU
    have hc : (univ \ univ.image (blockSiteRoot M p)).card = p-M := by
      rw [card_sdiff_of_subset (subset_univ _),card_univ,ZMod.card,hcard]
    rw [hc] at hh
    have hrec := (unoccupied_reciprocal_estimates p M hsize hhalf).1
    calc
      _ ≤ 2*(I.card : ℝ)/((p-M : ℕ) : ℝ)+2*(I.card : ℝ)/(p : ℝ) := hh
      _ ≤ 6*(I.card : ℝ)/(p : ℝ) := by
        have h := mul_le_mul_of_nonneg_left hrec (show 0 ≤ 2*(I.card : ℝ) by positivity)
        calc
          _ = (2*(I.card : ℝ))*(1/((p-M : ℕ) : ℝ))+2*(I.card : ℝ)/(p : ℝ) := by ring
          _ ≤ (2*(I.card : ℝ))*(2/(p : ℝ))+2*(I.card : ℝ)/(p : ℝ) := add_le_add h le_rfl
          _ = _ := by ring
      _ ≤ _ := le_add_of_nonneg_left (by positivity)
  · rw [ite_eq_right hbad,add_zero]
    obtain ⟨hinj,havoid⟩ := candidate_good_prime_roots I hp hbad
    have hn (e : BlockCandidateIndex M) (he : e ∈ I) :
        candidateModRoot p e ∉ univ.image (blockSiteRoot M p) := by
      rintro h
      obtain ⟨s,_,hs⟩ := mem_image.mp h
      exact havoid e he s hs.symm
    have hh := restrictedRootMass_l1_good I (candidateModRoot p) hinj
      (univ.image (blockSiteRoot M p)) (by rwa [hcard]) (by rwa [hcard]) hn
    simpa only [outsideCandidatePrimeMass,hcard] using hh

end JointDickman

end OAI
