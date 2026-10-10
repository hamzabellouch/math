import OAI.Combinatorics.ContingencyTables.Machines.EnumerationPointBounds
import OAI.Combinatorics.ContingencyTables.Sampling.OriginalTableEnumeration

namespace OAI

/-! # Binary size of one candidate in the original-table enumeration -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms Polynomial

lemma originalCandidates_length (z : CompletionMargins) :
    (originalCandidates z).length=gridStateCount (originalEnumerationData z) := by
  simp only [originalCandidates,List.length_map,gridWords,List.length_range]

theorem originalCandidates_point_polynomial : ∃ p : Polynomial ℕ,∀ z v,
    v∈originalCandidates z → weight v ≤ p.eval (weight z) := by
  obtain ⟨p,hp⟩ := polynomial_originalEnumerationData
  obtain ⟨q,hq⟩ := polynomial_originalCandidate
  let word : Polynomial ℕ := p*(4*p+2)+1
  refine ⟨q.comp (1+X+word),?_⟩
  intro z v hv
  rw [originalCandidates] at hv
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hv
  have hdata : weight (originalEnumerationData z) ≤ p.eval (weight z) :=
    (Nat.le_add_left _ _).trans (hp z)
  have hlen : (originalEnumerationData z).1.length ≤ p.eval (weight z) :=
    (list_length_le_weight _).trans ((weight_fst _).trans hdata)
  have hbase : weight (originalEnumerationData z).2 ≤ p.eval (weight z) :=
    (weight_snd _).trans hdata
  have hword := gridWords_point_weight (originalEnumerationData z) (by
    change 0 < (originalLayoutMargins z).1.sum+1
    omega) w hw
  have hw' : weight w ≤ word.eval (weight z) := by
    apply hword.trans
    simp only [word,eval_add,eval_mul,eval_ofNat,eval_one]
    exact Nat.add_le_add_right (Nat.mul_le_mul hlen (by omega)) 1
  have hin : weight (z,w) ≤ (1+X+word).eval (weight z) := by
    simp only [weight_prod,eval_add,eval_one,eval_X]
    omega
  simpa only [eval_comp] using
    (Nat.le_add_left _ _).trans ((hq (z,w)).trans (polynomial_eval_monotone q hin))

end ContingencyTables.ProfilePrograms

end OAI
