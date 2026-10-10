import OAI.Probability.MatroidProphet.Main

namespace OAI

/-!
Source-facing contracts for the candidate filter (setup.tex, Lemma `lem:filter`).
The sets below are the actual rounded-priority greedy survivors and candidate
labels, not arbitrary sets satisfying a desired inequality. The fair-mask law
is the concrete product law `bitsExpectation` on the entire labeled ground set.
-/

namespace MatroidProphet.CandidateContracts

open Finset MainAlgorithm

/-- The full candidate-mass contract, including pointwise independence and
containment for every mask. No positivity premise is needed here because the
rounding map itself discards nonpositive coordinates. -/
theorem candidate_mass {n : ℕ} (M : Matroid (Fin n))
    (hE : M.E = Set.univ) (w : Weights n) :
    let a := fun e => roundedLevel weightBase (w e)
    let Y := fun H => positiveGreedy M a \ H
    let U := candidateLabels M a
    (∀ H, M.Indep (Y H : Set (Fin n)) ∧ Y H ⊆ U H) ∧
    bitsExpectation (fun _ => (1 / 2 : ℝ)) Finset.univ
      (fun H => ∑ e ∈ Y H, roundedWeight weightBase (w e)) =
        optimum M (fun e => roundedWeight weightBase (w e)) / 2 ∧
    bitsExpectation (fun _ => (1 / 2 : ℝ)) Finset.univ
      (fun H => ∑ e ∈ U H, roundedWeight weightBase (w e)) ≤
        optimum M (fun e => roundedWeight weightBase (w e)) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro H
    exact ⟨positiveGreedy_survivors_indep M hE _ H,
      positiveGreedy_survivors_subset M _ H⟩
  · exact expectation_positiveGreedy_survivors M hE w (by norm_num [weightBase])
  · exact expectation_candidateLabels_le_optimum M hE w weightBase

/-- Both inequalities of the source's rounding bound, together with an actual
independent positive-priority greedy maximizer. This includes zero weights,
loops, ties, the empty ground set, and rank zero. -/
theorem rounding_and_greedy {n : ℕ} (M : Matroid (Fin n))
    (hE : M.E = Set.univ) (w : Weights n) (hw : ∀ e, 0 ≤ w e) :
    let u := fun e => roundedWeight weightBase (w e)
    let I := positiveGreedy M (fun e => roundedLevel weightBase (w e))
    optimum M w / weightBase ≤ optimum M u ∧
    optimum M u ≤ optimum M w ∧
    M.Indep (I : Set (Fin n)) ∧
    (∑ e ∈ I, u e) = optimum M u := by
  dsimp only
  have hB : (1 : ℝ) < weightBase := by norm_num [weightBase]
  refine ⟨?_, ?_, positiveGreedy_indep M hE _, ?_⟩
  · apply (div_le_iff₀ (zero_lt_one.trans hB)).2
    simpa only [mul_comm] using optimum_rounding_bound M weightBase hB w hw
  · exact optimum_mono M _ w (fun e => roundedWeight_le hB (hw e))
  · change (∑ e ∈ positiveGreedy M (fun e => roundedLevel weightBase (w e)),
      levelWeight weightBase (roundedLevel weightBase (w e))) = _
    rw [sum_positiveGreedy]
    exact Priority.rounded_greedy_optimal M hE w hB

/-- The actual candidate predicate never includes a loop or a nonpositive label.
This is a pointwise statement for every mask, not only almost surely. -/
theorem candidate_positive_nonloop {n : ℕ} (M : Matroid (Fin n))
    (w : Weights n) (H : Finset (Fin n)) (e : Fin n)
    (he : e ∈ candidateLabels M (fun f => roundedLevel weightBase (w f)) H) :
    0 < w e ∧ e ∉ H ∧ e ∉ M.closure ∅ := by
  classical
  have hc : candidate M ⟨H, ∅, ∅, ∅, false⟩
      (fun f => roundedLevel weightBase (w f)) e (roundedLevel weightBase (w e)) :=
    (Finset.mem_filter.mp he).2
  refine ⟨?_, hc.2.1, candidate_not_mem_closure_empty M _ _ _ _ hc⟩
  by_contra hn
  exact hc.1 (by simp [roundedLevel, hn])

end MatroidProphet.CandidateContracts

end OAI
