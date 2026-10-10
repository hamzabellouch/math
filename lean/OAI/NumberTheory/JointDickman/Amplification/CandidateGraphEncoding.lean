import OAI.NumberTheory.JointDickman.Amplification.ArithmeticCandidateWeight
import OAI.NumberTheory.JointDickman.Amplification.GraphTripleSupport

namespace OAI

/-! # Encoding endpoint candidates as the original graph's coefficient triples -/

namespace JointDickman
open Finset Classical

noncomputable def candidateGraphTriple {M : ℕ} (B : ℕ) (e : BlockCandidateIndex M) :
    GraphCoefficientTriple := (coefficientPrimeSet B (candidateQuotient e),e.2.2,e.2.1)

theorem candidateLag_pos {B L T H M : ℕ} {τ C : ℝ} {e : BlockCandidateIndex M}
    (he : BlockCandidateAdmissible B L T H τ C e) : 0 < candidateLag e := by
  unfold candidateLag
  exact Nat.sub_pos_of_lt he.1

theorem candidateGraphTriple_lag {B L T H M : ℕ} {τ C : ℝ}
    {e : BlockCandidateIndex M} (he : BlockCandidateAdmissible B L T H τ C e) :
    graphTripleLag (candidateGraphTriple B e) = (candidateLag e : ℤ) := by
  have hq := he.2.2.2.2.2.2.2.2.1
  have hq0 : (candidateQuotient e : ℤ) ≠ 0 := by exact_mod_cast he.2.2.2.1.ne'
  have heq : (candidateHigh e : ℤ)-candidateLow e =
      (candidateLag e : ℤ)*candidateQuotient e := by
    have h : (candidateHigh e : ℤ) = candidateLow e+(candidateLag e : ℤ)*candidateQuotient e := by
      exact_mod_cast he.2.2.2.2.1
    linarith
  change ((candidateHigh e : ℤ)-candidateLow e)/
    ((∏ p ∈ coefficientPrimeSet B (candidateQuotient e), p : ℕ) : ℤ) = _
  rw [← hq,heq,Int.mul_ediv_cancel _ hq0]

theorem candidateGraphTriple_mem {B L T H M : ℕ} {τ C : ℝ}
    (S : Fin M → Finset ℕ) (hS : ∀ i, S i ⊆ auxiliaryPrimes B)
    (hT : T ≤ auxiliaryCutoff B) {e : BlockCandidateIndex M}
    (he : e ∈ blockCandidates B L T H M τ C S) :
    candidateGraphTriple B e ∈ arithmeticGraphTriples B T := by
  obtain ⟨hs,ha⟩ := mem_blockCandidates.mp he
  have hlo := (mem_endpointSplits.mp hs.1).1.trans (hS e.1.1)
  have hhi := (mem_endpointSplits.mp hs.2).1.trans (hS e.1.2)
  have hj := candidateLag_pos ha
  have hq := ha.2.2.2.2.2.2.2.2.1
  have hab : e.2.2 ≠ e.2.1 := by
    intro hab
    have hsame : candidateHigh e = candidateLow e := by
      change (∏ p ∈ e.2.2, p) = ∏ p ∈ e.2.1, p
      rw [hab]
    have hrel := ha.2.2.2.2.1
    have hc := ha.2.2.2.1
    nlinarith
  apply mem_filter.mpr
  refine ⟨mem_product.mpr ⟨mem_powerset.mpr (filter_subset _ _),
    mem_product.mpr ⟨mem_powerset.mpr hhi,mem_powerset.mpr hlo⟩⟩,?_⟩
  unfold GraphCoefficientAdmissible
  change e.2.2 ≠ e.2.1 ∧ graphTripleLag (candidateGraphTriple B e) ≠ 0 ∧
    (graphTripleLag (candidateGraphTriple B e)).natAbs < T ∧
    (candidateHigh e : ℤ)-candidateLow e = graphTripleLag (candidateGraphTriple B e)*
      ((∏ p ∈ coefficientPrimeSet B (candidateQuotient e), p : ℕ) : ℤ) ∧
    (candidateHigh e).Coprime (graphTripleLag (candidateGraphTriple B e)).natAbs
  rw [candidateGraphTriple_lag ha,Int.natAbs_natCast,← hq]
  refine ⟨hab,by exact_mod_cast hj.ne',ha.2.2.1,?_,?_⟩
  · have hh : (candidateHigh e : ℤ) = candidateLow e+(candidateLag e : ℤ)*candidateQuotient e := by
      exact_mod_cast ha.2.2.2.2.1
    linarith
  · exact auxiliaryProduct_coprime_small hhi hj (ha.2.2.1.le.trans hT)

theorem candidateGraphTriple_weight {B L T H M u : ℕ} {τ C : ℝ}
    {e : BlockCandidateIndex M}
    (he : e ∈ blockCandidates B L T H M τ C
      (fun i => coefficientPrimeSet B (u+(i.val+1))))
    (hsq : ¬ BlockSquareHit B M u) :
    graphTripleWeight B L τ C T (candidateGraphTriple B e) (u+(e.1.1.val+1))/(B : ℝ) =
      candidateRootWeight B L τ C (fun i => coefficientPrimeSet B (u+(i.val+1)))
        (candidateCutoff (amplificationOuterWeight B) (amplificationInnerWeight T)) e
        (coefficientPrimeSet B (divisorEdgeInverse (candidateHigh e) (candidateLow e)
          (candidateQuotient e) (u+(e.1.1.val+1)))) := by
  have ha := (mem_blockCandidates.mp he).2
  have hq := ha.2.2.2.2.2.2.2.2.1
  unfold graphTripleWeight
  rw [candidateGraphTriple_lag ha]
  change arithmeticGraphPairWeight B L τ C _ _ _ _
    (∏ p ∈ coefficientPrimeSet B (candidateQuotient e), p) _ _ / _ = _
  rw [← hq]
  exact arithmetic_graph_candidate_weight _ _ he hsq

end JointDickman

end OAI
