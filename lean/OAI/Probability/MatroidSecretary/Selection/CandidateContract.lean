import OAI.Probability.MatroidProphet.Main

namespace OAI

namespace MatroidProphet.SourceContracts

open Finset Set MainAlgorithm

/-- Positive rounding does not remove a positive weight or create one at zero. -/
theorem roundedWeight_pos_iff {B x : ℝ} (hB : 0 < B) :
    0 < roundedWeight B x ↔ 0 < x := by
  unfold roundedWeight roundedLevel
  by_cases hx : 0 < x
  · rw [ite_eq_left hx, levelWeight]
    exact iff_of_true (zpow_pos hB _) hx
  · rw [ite_eq_right hx, levelWeight]
    exact iff_of_false (lt_irrefl 0) hx

/-- The actual candidate test is exactly `eq:candidates`, with higher rounded
levels taking priority and the original fixed label order breaking ties. -/
theorem mem_candidateLabels_iff {n : ℕ} (M : Matroid (Fin n))
    (w : Weights n) (B : ℝ) (H : Finset (Fin n)) (e : Fin n) :
    e ∈ candidateLabels M (fun f => roundedLevel B (w f)) H ↔
      0 < w e ∧ e ∉ H ∧
        e ∉ M.closure {f | f ∈ H ∧
          higher f (roundedLevel B (w f)) e (roundedLevel B (w e))} := by
  classical
  have hpos : roundedLevel B (w e) ≠ none ↔ 0 < w e := by
    simp [roundedLevel]
  constructor
  · intro hcandidate
    obtain ⟨hlevel, houtside, hclosure⟩ := (Finset.mem_filter.mp hcandidate).2
    exact ⟨hpos.mp hlevel, houtside, hclosure⟩
  · rintro ⟨hpositive, houtside, hclosure⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hpos.mpr hpositive, houtside, hclosure⟩

/-- The same test in the source's literal `u_e > 0` notation. -/
theorem mem_candidateLabels_iff_rounded {n : ℕ} (M : Matroid (Fin n))
    (w : Weights n) {B : ℝ} (hB : 0 < B) (H : Finset (Fin n)) (e : Fin n) :
    e ∈ candidateLabels M (fun f => roundedLevel B (w f)) H ↔
      0 < roundedWeight B (w e) ∧ e ∉ H ∧
        e ∉ M.closure {f | f ∈ H ∧
          higher f (roundedLevel B (w f)) e (roundedLevel B (w e))} := by
  rw [roundedWeight_pos_iff hB]
  exact mem_candidateLabels_iff M w B H e

/-- Candidates cannot be loops, including when loops have positive weights. -/
theorem candidateLabels_nonloop {n : ℕ} (M : Matroid (Fin n))
    (a : Fin n → Option ℤ) (H : Finset (Fin n)) (e : Fin n)
    (he : e ∈ candidateLabels M a H) : e ∉ M.closure ∅ := by
  classical
  exact candidate_not_mem_closure_empty M ⟨H, ∅, ∅, ∅, false⟩ a e (a e)
    (Finset.mem_filter.mp he).2

/-- Both deterministic assertions and both expectation assertions in `lem:filter`.
The assumptions include no positive-rank, nonempty-ground, or no-ties condition. -/
theorem candidate_mass {n : ℕ} (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (w : Weights n) (_hw : ∀ e, 0 ≤ w e) {B : ℝ} (hB : 1 < B) :
    (∀ H : Finset (Fin n),
      M.Indep ((positiveGreedy M (fun e => roundedLevel B (w e)) \ H :
        Finset (Fin n)) : Set (Fin n)) ∧
      positiveGreedy M (fun e => roundedLevel B (w e)) \ H ⊆
        candidateLabels M (fun e => roundedLevel B (w e)) H) ∧
    bitsExpectation (fun _ => (1 / 2 : ℝ)) Finset.univ
      (fun H => ∑ e ∈ positiveGreedy M (fun e => roundedLevel B (w e)) \ H,
        roundedWeight B (w e)) = optimum M (fun e => roundedWeight B (w e)) / 2 ∧
    bitsExpectation (fun _ => (1 / 2 : ℝ)) Finset.univ
      (fun H => ∑ e ∈ candidateLabels M (fun e => roundedLevel B (w e)) H,
        roundedWeight B (w e)) ≤ optimum M (fun e => roundedWeight B (w e)) := by
  refine ⟨?_, expectation_positiveGreedy_survivors M hE w hB,
    expectation_candidateLabels_le_optimum M hE w B⟩
  intro H
  exact ⟨positiveGreedy_survivors_indep M hE _ H,
    positiveGreedy_survivors_subset M _ H⟩

/-- The two-sided optimum rounding estimate `eq:rounding`, including zero weights. -/
theorem optimum_rounding {n : ℕ} (M : Matroid (Fin n))
    (w : Weights n) (hw : ∀ e, 0 ≤ w e) {B : ℝ} (hB : 1 < B) :
    optimum M w / B ≤ optimum M (fun e => roundedWeight B (w e)) ∧
      optimum M (fun e => roundedWeight B (w e)) ≤ optimum M w := by
  constructor
  · apply (div_le_iff₀ (zero_lt_one.trans hB)).2
    simpa only [mul_comm] using optimum_rounding_bound M B hB w hw
  · exact optimum_mono M _ w (fun e => roundedWeight_le hB (hw e))

end MatroidProphet.SourceContracts

end OAI
