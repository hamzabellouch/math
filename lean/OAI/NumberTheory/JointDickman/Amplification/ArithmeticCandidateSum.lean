import OAI.NumberTheory.JointDickman.Amplification.GraphCandidateDecoding

namespace OAI

/-! # Exact reindexing of the arithmetic graph by its endpoint candidates -/

namespace JointDickman
open Finset Classical

noncomputable def arithmeticCandidateWeight (B L T : ℕ) (τ C : ℝ)
    {M : ℕ} (u : ℕ) (e : BlockCandidateIndex M) : ℝ :=
  candidateRootWeight B L τ C (fun i => coefficientPrimeSet B (u+(i.val+1)))
    (candidateCutoff (amplificationOuterWeight B) (amplificationInnerWeight T)) e
    (coefficientPrimeSet B (divisorEdgeInverse (candidateHigh e) (candidateLow e)
      (candidateQuotient e) (u+(e.1.1.val+1))))

theorem rawArithmeticGraphKernel_candidate_sum {B L T H M N u : ℕ} {τ C : ℝ}
    (hB : 0 < B) (hT : 0 < T) (hTP : T ≤ auxiliaryCutoff B)
    {i k : Fin M} (hik : i < k) (hH : H < k.val-i.val)
    (hsq : ¬ BlockSquareHit B M u) :
    rawArithmeticGraphKernel B L τ C T N ((k.val-i.val : ℕ) : ℤ)
        (u+(i.val+1))/(B : ℝ) =
      ∑ e ∈ blockCandidates B L T H M τ C
          (fun l => coefficientPrimeSet B (u+(l.val+1))),
        if e.1 = (i,k) ∧ u+(i.val+1) ∈ graphTripleEdges N (candidateGraphTriple B e)
        then arithmeticCandidateWeight B L T τ C u e else 0 := by
  unfold rawArithmeticGraphKernel
  rw [sum_div]
  let f (g : GraphCoefficientTriple) : ℝ :=
    (if graphTripleLag g = ((k.val-i.val : ℕ) : ℤ) ∧
        u+(i.val+1) ∈ graphTripleEdges N g
      then graphTripleWeight B L τ C T g (u+(i.val+1)) else 0)/(B : ℝ)
  have hsupport (g : GraphCoefficientTriple) (hf : f g ≠ 0) :
      graphTripleLag g = ((k.val-i.val : ℕ) : ℤ) ∧
      u+(i.val+1) ∈ graphTripleEdges N g ∧
      graphTripleWeight B L τ C T g (u+(i.val+1)) ≠ 0 := by
    dsimp [f] at hf
    by_cases h : graphTripleLag g = ((k.val-i.val : ℕ) : ℤ) ∧
        u+(i.val+1) ∈ graphTripleEdges N g
    · refine ⟨h.1,h.2,?_⟩
      intro hz
      simp [h,hz] at hf
    · simp [h] at hf
  apply sum_bij_ne_zero (fun g _ _ => graphBlockCandidate i k g)
  · intro g hg hf
    obtain ⟨hlag,hn,hw⟩ := hsupport g hf
    exact graphBlockCandidate_mem hB hT hik hH hg hlag hn hw hsq
  · intro g hg hf g' hg' hf' heq
    have hs := hsupport g hf
    have hs' := hsupport g' hf'
    have hr := graphBlockCandidate_roundtrip hik
      (graphTripleWeight_nonzero_supported hB hT τ C hg hs.1 hs.2.2)
    have hr' := graphBlockCandidate_roundtrip hik
      (graphTripleWeight_nonzero_supported hB hT τ C hg' hs'.1 hs'.2.2)
    exact hr.symm.trans ((congrArg (candidateGraphTriple B) heq).trans hr')
  · intro e he hwe
    have hp : e.1 = (i,k) ∧
        u+(i.val+1) ∈ graphTripleEdges N (candidateGraphTriple B e) := by
      by_contra h
      simp only [ite_eq_right h,ne_eq,not_true_eq_false] at hwe
    have hg := candidateGraphTriple_mem _ (fun l => filter_subset _ _) hTP he
    have ha := (mem_blockCandidates.mp he).2
    have hj : candidateLag e = k.val-i.val := by
      change e.1.2.val-e.1.1.val = _
      rw [hp.1]
    have hlag : graphTripleLag (candidateGraphTriple B e) = ((k.val-i.val : ℕ) : ℤ) :=
      (candidateGraphTriple_lag ha).trans (congrArg (fun j : ℕ => (j : ℤ)) hj)
    refine ⟨candidateGraphTriple B e,hg,?_,candidateGraphTriple_roundtrip hp.1⟩
    have heweight := candidateGraphTriple_weight he hsq
    have hilow : e.1.1 = i := congrArg Prod.fst hp.1
    change _ = arithmeticCandidateWeight B L T τ C u e at heweight
    rw [hilow] at heweight
    dsimp [f]
    rw [ite_eq_left ⟨hlag,hp.2⟩,heweight]
    simpa only [ite_eq_left hp] using hwe
  · intro g hg hf
    obtain ⟨hlag,hn,hw⟩ := hsupport g hf
    have hs := graphTripleWeight_nonzero_supported hB hT τ C hg hlag hw
    have he := graphBlockCandidate_mem hB hT hik hH hg hlag hn hw hsq
    have hr := graphBlockCandidate_roundtrip hik hs
    have hwgt := candidateGraphTriple_weight he hsq
    change _ = arithmeticCandidateWeight B L T τ C u (graphBlockCandidate i k g) at hwgt
    rw [hr] at hwgt
    rw [ite_eq_left ⟨hlag,hn⟩,ite_eq_left (show
      (graphBlockCandidate i k g).1 = (i,k) ∧
        u+(i.val+1) ∈ graphTripleEdges N (candidateGraphTriple B (graphBlockCandidate i k g))
      from ⟨rfl,hr.symm ▸ hn⟩)]
    exact hwgt

end JointDickman

end OAI
