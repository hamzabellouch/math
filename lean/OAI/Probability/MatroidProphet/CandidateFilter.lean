import OAI.Probability.MatroidProphet.Priority

namespace OAI

namespace MatroidProphet.MainAlgorithm

open Finset Set

variable {n : ℕ}

noncomputable def candidateSet (M : Matroid (Fin n)) (d : MainMasks n)
    (a : Fin n → Option ℤ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun e => candidate M d a e (a e)

noncomputable def candidateLabels (M : Matroid (Fin n)) (a : Fin n → Option ℤ)
    (H : Finset (Fin n)) : Finset (Fin n) := candidateSet M ⟨H, ∅, ∅, ∅, false⟩ a

lemma candidateSet_eq_candidateLabels (M : Matroid (Fin n)) (d : MainMasks n)
    (a : Fin n → Option ℤ) : candidateSet M d a = candidateLabels M a d.H := rfl

lemma candidate_congr_observed (M : Matroid (Fin n)) (d : MainMasks n)
    (a seen : Fin n → Option ℤ) (hseen : ∀ f ∈ d.H, seen f = a f)
    (e : Fin n) (x : Option ℤ) : candidate M d seen e x ↔ candidate M d a e x := by
  have hs : {f | f ∈ d.H ∧ higher f (seen f) e x} =
      {f | f ∈ d.H ∧ higher f (a f) e x} := by
    ext f
    by_cases hf : f ∈ d.H
    · simp [hf, hseen f hf]
    · simp [hf]
  simp only [candidate, hs]

lemma candidateSet_eq_filter (M : Matroid (Fin n)) (d : MainMasks n)
    (a : Fin n → Option ℤ) :
    candidateSet M d a =
      (Candidates.candidates M (Priority.time a) Finset.univ d.H).filter (fun e => a e ≠ none) := by
  classical
  ext e
  by_cases ha : a e = none
  · constructor
    · intro he
      exact False.elim (((Finset.mem_filter.mp he).2).1 ha)
    · intro he
      exact False.elim ((Finset.mem_filter.mp he).2 ha)
  · have hs : {f | f ∈ d.H ∧ higher f (a f) e (a e)} =
        Candidates.prior (Priority.time a) d.H e := by
      ext f
      simp only [Candidates.prior, Set.mem_ofPred_eq, Priority.main_higher_iff_time a f e ha]
    simp [candidateSet, candidate, Candidates.candidates, ha, hs, and_comm, and_left_comm]

lemma sum_candidateLabels (M : Matroid (Fin n)) (a : Fin n → Option ℤ)
    (H : Finset (Fin n)) (B : ℝ) :
    (∑ e ∈ candidateLabels M a H, levelWeight B (a e)) =
      ∑ e ∈ Candidates.candidates M (Priority.time a) Finset.univ H, levelWeight B (a e) := by
  classical
  rw [candidateLabels, candidateSet_eq_filter]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro e he hnot
  have hz : a e = none := by simpa only [Finset.mem_filter, he, true_and, not_not] using hnot
  simp [hz, levelWeight]

noncomputable def positiveGreedy (M : Matroid (Fin n)) (a : Fin n → Option ℤ) : Finset (Fin n) := by
  classical
  exact (Candidates.greedy M (Priority.time a) Finset.univ).filter fun e => a e ≠ none

lemma positiveGreedy_indep (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (a : Fin n → Option ℤ) : M.Indep (positiveGreedy M a : Set (Fin n)) := by
  apply (Candidates.greedy_indep M (Priority.time a) (Priority.time_injective a)
    Finset.univ (fun e _ => by simp [hE])).subset
  exact Finset.filter_subset _ _

lemma positiveGreedy_survivors_subset (M : Matroid (Fin n)) (a : Fin n → Option ℤ)
    (H : Finset (Fin n)) : positiveGreedy M a \ H ⊆ candidateLabels M a H := by
  classical
  intro e he
  obtain ⟨heG, heH⟩ := Finset.mem_sdiff.mp he
  obtain ⟨heFull, hea⟩ := Finset.mem_filter.mp heG
  have heC := Candidates.greedy_sdiff_subset_candidates M (Priority.time a) Finset.univ H
    (Finset.subset_univ H) (Finset.mem_sdiff.mpr ⟨heFull, heH⟩)
  rw [candidateLabels, candidateSet_eq_filter]
  exact Finset.mem_filter.mpr ⟨heC, hea⟩

lemma sum_positiveGreedy (M : Matroid (Fin n)) (a : Fin n → Option ℤ) (B : ℝ) :
    (∑ e ∈ positiveGreedy M a, levelWeight B (a e)) =
      ∑ e ∈ Candidates.greedy M (Priority.time a) Finset.univ, levelWeight B (a e) := by
  classical
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro e he hnot
  have hz : a e = none := by simpa only [positiveGreedy, Finset.mem_filter, he,
    true_and, not_not] using hnot
  simp [hz, levelWeight]

theorem expectation_positiveGreedy_survivors (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (w : Weights n) {B : ℝ} (hB : 1 < B) :
    bitsExpectation (fun _ => (1 / 2 : ℝ)) Finset.univ
      (fun H => ∑ e ∈ positiveGreedy M (fun e => roundedLevel B (w e)) \ H,
        roundedWeight B (w e)) = optimum M (fun e => roundedWeight B (w e)) / 2 := by
  rw [Candidates.expectation_sdiff_fair Finset.univ _ (Finset.subset_univ _) _]
  rw [show (∑ e ∈ positiveGreedy M (fun e => roundedLevel B (w e)), roundedWeight B (w e)) =
      ∑ e ∈ Candidates.greedy M (Priority.time (fun e => roundedLevel B (w e))) Finset.univ,
        roundedWeight B (w e) from sum_positiveGreedy M _ B]
  rw [Priority.rounded_greedy_optimal M hE w hB]

theorem expectation_candidateLabels_le_optimum (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (w : Weights n) (B : ℝ) :
    bitsExpectation (fun _ => (1 / 2 : ℝ)) Finset.univ
      (fun H => ∑ e ∈ candidateLabels M (fun e => roundedLevel B (w e)) H,
        roundedWeight B (w e)) ≤ optimum M (fun e => roundedWeight B (w e)) := by
  have heq : bitsExpectation (fun _ => (1 / 2 : ℝ)) Finset.univ
      (fun H => ∑ e ∈ candidateLabels M (fun e => roundedLevel B (w e)) H,
        roundedWeight B (w e)) =
      bitsExpectation (fun _ => (1 / 2 : ℝ)) Finset.univ
      (fun H => ∑ e ∈ Candidates.candidates M (Priority.time (fun e => roundedLevel B (w e)))
        Finset.univ H, roundedWeight B (w e)) := by
    apply bitsExpectation_congr
    intro H _
    exact sum_candidateLabels M _ H B
  rw [heq]
  exact Candidates.expectation_candidates_le_optimum M _ (Priority.time_injective _)
    Finset.univ (fun e _ => by simp [hE]) _

lemma candidate_observed_hidden (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (w : Weights n) (r : Seed (mainSeedBits n)) (e : Fin n) (x : Option ℤ) (B : ℝ) :
    candidate M (mainMasks r)
      (fun f => roundedLevel B (observed (hidden M hE) r w f)) e x ↔
    candidate M (mainMasks r) (fun f => roundedLevel B (w f)) e x := by
  apply candidate_congr_observed
  intro f hf
  have hm : f ∈ (hidden M hE).mask r :=
    Finset.mem_union_left _ (Finset.mem_union_left _ hf)
  simp only [observed, ite_eq_left hm]

lemma positiveGreedy_survivors_indep (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (a : Fin n → Option ℤ) (H : Finset (Fin n)) :
    M.Indep ((positiveGreedy M a \ H : Finset (Fin n)) : Set (Fin n)) :=
  (positiveGreedy_indep M hE a).subset (fun _ he => (Finset.mem_sdiff.mp he).1)

lemma candidate_not_mem_closure_empty (M : Matroid (Fin n)) (d : MainMasks n)
    (seen : Fin n → Option ℤ) (e : Fin n) (x : Option ℤ)
    (he : candidate M d seen e x) : e ∉ M.closure ∅ := by
  intro hm
  exact he.2.2 (M.closure_subset_closure (Set.empty_subset _) hm)

lemma candidate_singleton_indep (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (seen : Fin n → Option ℤ) (e : Fin n) (x : Option ℤ)
    (he : candidate M d seen e x) : M.Indep ({e} : Set (Fin n)) := by
  have hn := candidate_not_mem_closure_empty M d seen e x he
  simpa using (M.empty_indep.insert_indep_iff_of_notMem (by simp : e ∉ (∅ : Set (Fin n)))).2
    ⟨by simp [hE], hn⟩

end MatroidProphet.MainAlgorithm

end OAI
