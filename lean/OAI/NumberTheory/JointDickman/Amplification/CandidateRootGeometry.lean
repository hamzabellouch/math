import OAI.NumberTheory.JointDickman.Amplification.RationalCandidateRoots

namespace OAI

/-! # Uniqueness of a representation at a fixed pair of endpoints -/

namespace JointDickman
open Finset

open Classical in
theorem mem_blockCandidatePool {B L M : ℕ} {τ C : ℝ} {S : Fin M → Finset ℕ}
    {e : BlockCandidateIndex M} :
    e ∈ blockCandidatePool B L M τ C S ↔
      e.2.1 ∈ endpointSplits B L τ C (S e.1.1) ∧
      e.2.2 ∈ endpointSplits B L τ C (S e.1.2) := by
  unfold blockCandidatePool
  constructor
  · intro h
    obtain ⟨ik,_,h⟩ := mem_biUnion.mp h
    obtain ⟨ab,hab,he⟩ := mem_image.mp h
    subst e
    simpa only [Finset.product_eq_sprod,mem_product] using hab
  · rintro ⟨hlo,hhi⟩
    apply mem_biUnion.mpr
    refine ⟨e.1,mem_univ _,mem_image.mpr ⟨e.2,?_,by cases e; rfl⟩⟩
    simpa only [Finset.product_eq_sprod,mem_product] using And.intro hlo hhi

open Classical in
theorem mem_blockCandidates {B L T H M : ℕ} {τ C : ℝ} {S : Fin M → Finset ℕ}
    {e : BlockCandidateIndex M} :
    e ∈ blockCandidates B L T H M τ C S ↔
      (e.2.1 ∈ endpointSplits B L τ C (S e.1.1) ∧
        e.2.2 ∈ endpointSplits B L τ C (S e.1.2)) ∧
      BlockCandidateAdmissible B L T H τ C e := by
  simp only [blockCandidates,mem_filter,mem_blockCandidatePool]

noncomputable def blockCandidateRoot {M : ℕ} (e : BlockCandidateIndex M) : ℚ :=
  shiftedCandidateRoot (candidateLow e) (candidateQuotient e) (e.1.1.val+1)

/-- On a fixed unordered pair the rational root specifies both endpoint
subset products, and hence the unique candidate representation. -/
theorem blockCandidate_same_pair_root_unique {B L T H M : ℕ} {τ C : ℝ}
    {S : Fin M → Finset ℕ} (hS : ∀ i, S i ⊆ auxiliaryPrimes B)
    {e f : BlockCandidateIndex M}
    (he : e ∈ blockCandidates B L T H M τ C S)
    (hf : f ∈ blockCandidates B L T H M τ C S)
    (hpair : e.1 = f.1) (hroot : blockCandidateRoot e = blockCandidateRoot f) : e = f := by
  obtain ⟨hes,hea⟩ := mem_blockCandidates.mp he
  obtain ⟨hfs,hfa⟩ := mem_blockCandidates.mp hf
  obtain ⟨_,_,_,hec,herel,_,hecop,_⟩ := hea
  obtain ⟨_,_,_,hfc,hfrel,_,hfcop,_⟩ := hfa
  have hlpos : e.1.1.val = f.1.1.val := congrArg (fun p : Fin M × Fin M => p.1.val) hpair
  have huniq := shiftedCandidateRoot_injective hec hfc hecop hfcop hroot
  have hlow : candidateLow e = candidateLow f := by
    have hz := huniq.2
    rw [hlpos] at hz
    simp only [sub_self,zero_mul,add_zero] at hz
    exact_mod_cast hz.symm
  have hhigh : candidateHigh e = candidateHigh f := by
    have hlag : candidateLag e = candidateLag f := congrArg
      (fun p : Fin M × Fin M => p.2.val-p.1.val) hpair
    rw [herel,hfrel,hlow,hlag,huniq.1]
  have heb := (mem_endpointSplits.mp hes.1).1.trans (hS _)
  have hfb := (mem_endpointSplits.mp hfs.1).1.trans (hS _)
  have hea' := (mem_endpointSplits.mp hes.2).1.trans (hS _)
  have hfa' := (mem_endpointSplits.mp hfs.2).1.trans (hS _)
  have hb : e.2.1 = f.2.1 := primeProduct_injective (auxiliaryPrimes_prime B) heb hfb hlow
  have ha : e.2.2 = f.2.2 := primeProduct_injective (auxiliaryPrimes_prime B) hea' hfa' hhigh
  exact Prod.ext hpair (Prod.ext hb ha)

end JointDickman

end OAI
