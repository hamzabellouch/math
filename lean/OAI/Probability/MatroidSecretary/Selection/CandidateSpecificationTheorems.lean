import OAI.Probability.MatroidSecretary.Selection.CandidateSpecification
import OAI.Probability.MatroidSecretary.Selection.CandidateContracts

namespace OAI

/-! Correspondence of the independent source definitions with the implemented
candidate filter and positive priority-greedy, followed by the source contract. -/

namespace MatroidProphet.CandidateSpecification

open Finset

lemma higher_eq_main {n : ℕ} (f : Fin n) (a : Option ℤ)
    (e : Fin n) (b : Option ℤ) :
    higher f a e b ↔ MainAlgorithm.higher f a e b := Iff.rfl

lemma candidates_eq_main {n : ℕ} (M : Matroid (Fin n))
    (a : Fin n → Option ℤ) (H : Finset (Fin n)) :
    candidates M a H = MainAlgorithm.candidateLabels M a H := by
  classical
  rw [MainAlgorithm.candidateLabels, MainAlgorithm.candidateSet_eq_filter]
  ext element
  by_cases hpositive : a element = none
  · simp [candidates, hpositive]
  · have hprior : {label | label ∈ H ∧ higher label (a label) element (a element)} =
        Candidates.prior (Priority.time a) H element := by
      ext label
      simp only [Candidates.prior, Set.mem_ofPred_eq, higher_eq_main,
        Priority.main_higher_iff_time a label element hpositive]
    simp [candidates, Candidates.candidates, hpositive, hprior]

lemma greedy_eq_main {n : ℕ} (M : Matroid (Fin n))
    (a : Fin n → Option ℤ) : greedy M a = MainAlgorithm.positiveGreedy M a := by
  classical
  ext e
  by_cases ha : a e = none
  · simp [greedy, MainAlgorithm.positiveGreedy, ha]
  · have hp : {f | higher f (a f) e (a e)} =
        Candidates.prior (Priority.time a) Finset.univ e := by
      ext f
      simp only [Candidates.prior, Finset.mem_univ, true_and,
        Set.mem_ofPred_eq, higher_eq_main, Priority.main_higher_iff_time a f e ha]
    simp [greedy, MainAlgorithm.positiveGreedy, Candidates.greedy, ha, hp]

lemma survivors_eq_main {n : ℕ} (M : Matroid (Fin n))
    (a : Fin n → Option ℤ) (H : Finset (Fin n)) :
    survivors M a H = MainAlgorithm.positiveGreedy M a \ H := by
  rw [survivors, greedy_eq_main]

 

theorem candidateMass : CandidateMass := by
  intro n M hE w
  simpa only [survivors_eq_main, candidates_eq_main] using
    CandidateContracts.candidate_mass M hE w

/-- Candidate membership uses only the focal key and keys on the revealed mask,
never another unobserved label's key. -/
lemma candidate_membership_congr {n : ℕ} (M : Matroid (Fin n))
    (a a' : Fin n → Option ℤ) (H : Finset (Fin n)) (e : Fin n)
    (he : a e = a' e) (hH : ∀ f ∈ H, a f = a' f) :
    e ∈ candidates M a H ↔ e ∈ candidates M a' H := by
  classical
  have hp : {f | f ∈ H ∧ higher f (a f) e (a e)} =
      {f | f ∈ H ∧ higher f (a' f) e (a' e)} := by
    ext f
    by_cases hf : f ∈ H
    · simp [hf, he, hH f hf]
    · simp [hf]
  simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hp, he]

/-- The source greedy definition really attains rounded OPT, with the source's
rounding comparison on both sides. This verifies the ancillary input `I*` rather
than assuming its optimality. -/
theorem source_rounding_and_greedy {n : ℕ} (M : Matroid (Fin n))
    (hE : M.E = Set.univ) (w : Weights n) (hw : ∀ e, 0 ≤ w e) :
    let u := fun e => roundedWeight weightBase (w e)
    let I := greedy M (fun e => roundedLevel weightBase (w e))
    optimum M w / weightBase ≤ optimum M u ∧
    optimum M u ≤ optimum M w ∧
    M.Indep (I : Set (Fin n)) ∧
    (∑ e ∈ I, u e) = optimum M u := by
  simpa only [greedy_eq_main] using CandidateContracts.rounding_and_greedy M hE w hw

end MatroidProphet.CandidateSpecification

end OAI
