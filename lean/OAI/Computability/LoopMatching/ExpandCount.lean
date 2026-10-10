import OAI.Computability.LoopMatching.ExpandBijection

namespace OAI

/-! Polynomial-time approximation of weighted matchings with singleton loops. -/

noncomputable section
open scoped BigOperators
namespace LoopMatching

lemma expanded_weight_zero_of_not_supported (G : Input) (j : ℕ)
    (N : (BinaryMatching.completeGraph (expand G j).n).Matching)
    (h : ¬ ∀ e ∈ N.val, e.val.1.val < G.n) :
    (∏ e ∈ N.val, BinaryMatching.multiplicity (expand G j) e) = 0 := by
  classical
  push Not at h
  obtain ⟨e, he, hl⟩ := h
  have heleft := e.val.1.isLt
  have heright := e.val.2.isLt
  have hord := e.property
  change e.val.1.val < e.val.2.val at hord
  simp only [expand_n] at heleft heright
  let f : BinaryMatching.Pair j :=
    ⟨(⟨e.val.1.val - G.n, by omega⟩,
      ⟨e.val.2.val - G.n, by omega⟩), by
        change e.val.1.val - G.n < e.val.2.val - G.n
        omega⟩
  have hf : dummyPair G j f = e := by
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext
    · dsimp [dummyPair, f]; omega
    · dsimp [dummyPair, f]; omega
  apply Finset.prod_eq_zero he
  rw [← hf]
  exact multiplicity_expand_dummy G j f

theorem expanded_count (G : Input) (j : ℕ) :
    BinaryMatching.count (expand G j) = j.factorial * countWithLoops G j := by
  classical
  let w : (BinaryMatching.completeGraph (expand G j).n).Matching → ℕ :=
    fun N => ∏ e ∈ N.val, BinaryMatching.multiplicity (expand G j) e
  have hzero :
      (∑ N : {N : (BinaryMatching.completeGraph (expand G j).n).Matching //
        ¬ ∀ e ∈ N.val, e.val.1.val < G.n}, w N.val) = 0 := by
    apply Finset.sum_eq_zero
    intro N _
    exact expanded_weight_zero_of_not_supported G j N.val N.property
  have hs : BinaryMatching.count (expand G j) =
      ∑ N : SupportedMatching G j, w N.val := by
    have ht := Fintype.sum_subtype_add_sum_subtype
      (fun N : (BinaryMatching.completeGraph (expand G j).n).Matching =>
        ∀ e ∈ N.val, e.val.1.val < G.n) w
    rw [hzero, Nat.add_zero] at ht
    have hi :
        (Subtype.fintype (fun N :
          (BinaryMatching.completeGraph (expand G j).n).Matching =>
            ∀ e ∈ N.val, e.val.1.val < G.n) : Fintype (SupportedMatching G j)) =
          supportedMatchingFintype G j := Subsingleton.elim _ _
    rw [hi] at ht
    exact ht.symm
  rw [hs]
  calc
    _ = ∑ q : (M : PartialMatching G.n) × (Fin j ≃ ↥(loopVertices M)),
        weight G q.1 := by
      apply Fintype.sum_equiv (supportedMatchingEquiv G j)
      intro N
      rw [supportedMatchingEquiv_fst]
      exact supported_matching_weight G j N
    _ = ∑ M : PartialMatching G.n,
        Fintype.card (Fin j ≃ ↥(loopVertices M)) * weight G M := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro M _
      simp
    _ = j.factorial * countWithLoops G j := by
      unfold countWithLoops
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro M _
      rw [card_dummyAssignments]
      by_cases h : (loopVertices M).card = j <;> simp [h]

end LoopMatching

end

end OAI
