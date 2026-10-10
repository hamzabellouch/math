import OAI.Combinatorics.MatchingPSD.MatchingConversion

namespace OAI

namespace PerfectMatchingPSD
open MatchingSmoothing Matrix
open scoped BigOperators
attribute [local instance] Classical.propDecidable

lemma perfectMatching_nonempty {n : ℕ} (hn : Even n) : Nonempty (PerfectMatching n) := by
  classical
  obtain ⟨k,hk⟩ := hn
  let e : (Fin k × Bool) ≃ Fin n := Fintype.equivOfCardEq (by
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    omega)
  exact ⟨fromPairing (Pairing.transport e standardPairing)⟩

lemma slack_le_vertices {n : ℕ} (hn : 1 ≤ n) (i : Row n) (M : PerfectMatching n) :
    slack i M ≤ (n:ℝ) := by
  rcases i with e | U
  · simp only [slack]
    split_ifs
    · exact_mod_cast hn
    · positivity
  · have hd := cut_degree_identity U.1 M
    have hcard : U.1.card ≤ n := by simpa using Finset.card_le_univ U.1
    have hc : crossingCount U.1 M ≤ n := by omega
    have hc' : (crossingCount U.1 M : ℝ) ≤ n := by exact_mod_cast hc
    change (crossingCount U.1 M : ℝ)-1 ≤ (n:ℝ)
    linarith

lemma normalized_factorization {n r : ℕ} (hn : Even n) (hnpos : 1 ≤ n)
    (hfac : HasFactorization n r) :
    ∃ (A : Row n → Matrix (Fin r) (Fin r) ℝ)
      (B : PerfectMatching n → Matrix (Fin r) (Fin r) ℝ),
      (∀ i, (A i).PosSemidef) ∧ (∀ M, (B M).PosSemidef) ∧
      (∀ i M, (A i*B M).trace = slack i M) ∧
      (∀ i, (A i).trace ≤ (n:ℝ)+1) ∧ (∀ M, (B M).trace ≤ (r:ℝ)) := by
  classical
  have := perfectMatching_nonempty hn
  rcases hfac with ⟨A,B,hA,hB,hpair⟩
  obtain ⟨A',B',hA',hB',hpair',htrA,htrB⟩ := exists_normalized_factors A B hA hB (n:ℝ)
    (fun i M => by rw [← hpair]; exact slack_le_vertices hnpos i M)
  exact ⟨A',B',hA',hB',fun i M => (hpair' i M).trans (hpair i M).symm,
    htrA,by simpa using htrB⟩

end PerfectMatchingPSD

end OAI
