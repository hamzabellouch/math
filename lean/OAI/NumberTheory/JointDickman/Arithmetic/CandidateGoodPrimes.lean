import OAI.NumberTheory.JointDickman.Arithmetic.CandidateDefectPrimes
import OAI.NumberTheory.JointDickman.Amplification.ConditionedRootComparison

namespace OAI

/-! # At every remaining prime the actual candidate roots are distinct -/

namespace JointDickman
open Finset

open Classical in
theorem candidateDefectPrimes_quotient_mem {B M p : ℕ}
    {I : Finset (BlockCandidateIndex M)} {e : BlockCandidateIndex M}
    (he : e ∈ I) (hp : p ∈ auxiliaryPrimes B) (hd : p ∣ candidateQuotient e) :
    p ∈ candidateDefectPrimes B I := by
  apply mem_biUnion.mpr
  refine ⟨e,he,mem_union.mpr (Or.inl (mem_union.mpr (Or.inl ?_)))⟩
  exact mem_filter.mpr ⟨hp,by simpa only [Int.natAbs_natCast] using hd⟩

open Classical in
theorem candidateDefectPrimes_site_mem {B M p : ℕ}
    {I : Finset (BlockCandidateIndex M)} {e : BlockCandidateIndex M}
    (he : e ∈ I) (hp : p ∈ auxiliaryPrimes B) (s : Fin M)
    (hd : p ∣ (candidateSiteValue e s).natAbs) : p ∈ candidateDefectPrimes B I := by
  apply mem_biUnion.mpr
  refine ⟨e,he,mem_union.mpr (Or.inl (mem_union.mpr (Or.inr ?_)))⟩
  exact mem_biUnion.mpr ⟨s,mem_univ _,mem_filter.mpr ⟨hp,hd⟩⟩

open Classical in
theorem candidateDefectPrimes_difference_mem {B M p : ℕ}
    {I : Finset (BlockCandidateIndex M)} {e f : BlockCandidateIndex M}
    (he : e ∈ I) (hf : f ∈ I) (hne : e ≠ f) (hp : p ∈ auxiliaryPrimes B)
    (hd : p ∣ (candidateRootDifference e f).natAbs) : p ∈ candidateDefectPrimes B I := by
  apply mem_biUnion.mpr
  refine ⟨e,he,mem_union.mpr (Or.inr (mem_biUnion.mpr ⟨f,hf,?_⟩))⟩
  rw [ite_eq_right hne]
  exact mem_filter.mpr ⟨hp,hd⟩

open Classical in
theorem candidate_good_prime_roots {B M p : ℕ} [Fact p.Prime]
    (I : Finset (BlockCandidateIndex M)) (hp : p ∈ auxiliaryPrimes B)
    (hgood : p ∉ candidateDefectPrimes B I) :
    Set.InjOn (candidateModRoot p) (I : Set (BlockCandidateIndex M)) ∧
      ∀ e ∈ I, ∀ s : Fin M, candidateModRoot p e ≠ blockSiteRoot M p s := by
  have hc (e : BlockCandidateIndex M) (he : e ∈ I) : ¬ p ∣ candidateQuotient e :=
    fun hd => hgood (candidateDefectPrimes_quotient_mem he hp hd)
  constructor
  · intro e he f hf hroot
    by_contra hne
    exact hgood (candidateDefectPrimes_difference_mem he hf hne hp
      (candidateModRoot_collision e f (hc e he) (hc f hf) hroot))
  · intro e he s hroot
    exact hgood (candidateDefectPrimes_site_mem he hp s
      (candidateModRoot_site_collision e s (hc e he) hroot))

open Classical in
theorem unoccupied_candidate_test_bound {B M p : ℕ} [Fact p.Prime]
    (I : Finset (BlockCandidateIndex M)) (hp : p ∈ auxiliaryPrimes B)
    (hgood : p ∉ candidateDefectPrimes B I) (hsize : M < p) (hhalf : 2*M ≤ p)
    (F : Finset (BlockCandidateIndex M) → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hF : ∀ S ∈ I.powerset, |F S| ≤ L) :
    |(∑ r ∈ univ \ (univ.image (blockSiteRoot M p)), F (rootHitSet I (candidateModRoot p) r))/
      ((p-M : ℕ) : ℝ) -
      ∑ S ∈ I.powerset, bernoulliSubsetMass I (fun _ => 1/(p : ℝ)) S * F S| ≤
        8*L*((I.card : ℝ)+(M : ℝ))^2/(p : ℝ)^2 := by
  have hcard : (univ.image (blockSiteRoot M p)).card = M := by
    rw [card_image_of_injective _ (blockSiteRoot_injective M p hsize),card_univ,Fintype.card_fin]
  obtain ⟨hinj,havoid⟩ := candidate_good_prime_roots I hp hgood
  have hnot (e : BlockCandidateIndex M) (he : e ∈ I) :
      candidateModRoot p e ∉ univ.image (blockSiteRoot M p) := by
    rintro h
    obtain ⟨s,_,hs⟩ := mem_image.mp h
    exact havoid e he s hs.symm
  have hh := unoccupied_roots_test_bound I (candidateModRoot p) hinj
    (univ.image (blockSiteRoot M p)) (by rwa [hcard]) (by rwa [hcard]) hnot F hL hF
  simpa only [hcard] using hh

end JointDickman

end OAI
