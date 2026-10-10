import OAI.Probability.SATComputability.CandidateProcess
import OAI.Probability.SATComputability.CandidateEncoding
import OAI.Probability.SATComputability.DeletionIncrement

namespace OAI

namespace FixedClauseThreshold.Computability

open Finset
open scoped Classical

def eraseCandidate {n : ℕ} (D : Finset (Fin n)) (x : DeletionCandidate n) :
    DeletionCandidate n := fun v => if v ∈ D then none else x v

def DeletionClosed {n : ℕ} (U : Finset (DeletionCandidate n)) : Prop :=
  ∀ x ∈ U, ∀ D : Finset (Fin n), eraseCandidate D x ∈ U

theorem literalFalse_of_erase {n : ℕ} {D : Finset (Fin n)}
    {x : DeletionCandidate n} {l : SignedLiteral n}
    (h : literalFalse (eraseCandidate D x) l) : literalFalse x l := by
  by_cases hl : l.1 ∈ D
  · simp [literalFalse, eraseCandidate, hl] at h
  · simpa only [literalFalse, eraseCandidate, ite_eq_right hl] using h

theorem candidateResidual_deletionClosed {n k d : ℕ}
    {U : Finset (DeletionCandidate n)} (hU : DeletionClosed U)
    (cs : Fin d → Fin k → SignedLiteral n) :
    DeletionClosed (candidateResidual U cs) := by
  intro x hx D
  obtain ⟨hxU, hx⟩ := Finset.mem_filter.mp hx
  apply Finset.mem_filter.mpr
  refine ⟨hU x hxU D, ?_⟩
  intro j hj
  exact hx j (fun l => literalFalse_of_erase (hj l))

def candidateSurvives {n : ℕ} (U : Finset (DeletionCandidate n))
    (D : Finset (Fin n)) : Prop := ∃ s : Fin n → Bool, encodeDeletion D s ∈ U

theorem eraseCandidate_encode {n : ℕ} {D E : Finset (Fin n)} (hDE : D ⊆ E)
    (s : Fin n → Bool) : eraseCandidate E (encodeDeletion D s) = encodeDeletion E s := by
  funext v
  by_cases hv : v ∈ E
  · simp [eraseCandidate, encodeDeletion, hv]
  · have hD : v ∉ D := fun h => hv (hDE h)
    simp [eraseCandidate, encodeDeletion, hv, hD]

theorem candidateSurvives_mono {n : ℕ} {U : Finset (DeletionCandidate n)}
    (hU : DeletionClosed U) {D E : Finset (Fin n)} (hDE : D ⊆ E)
    (hD : candidateSurvives U D) : candidateSurvives U E := by
  obtain ⟨s, hs⟩ := hD
  refine ⟨s, ?_⟩
  simpa only [eraseCandidate_encode hDE s] using hU _ hs E

theorem candidateSurvives_subset {n : ℕ} {U V : Finset (DeletionCandidate n)}
    (hUV : U ⊆ V) {D : Finset (Fin n)} (hU : candidateSurvives U D) :
    candidateSurvives V D := by
  obtain ⟨s, hs⟩ := hU
  exact ⟨s, hUV hs⟩

structure DeletionHistory (n M : ℕ) where
  state : ℕ → Finset (DeletionCandidate n)
  antitone : Antitone state
  closed : ∀ t, DeletionClosed (state t)
  capped : state M = ∅

theorem DeletionHistory.failure_exists {n M : ℕ} (H : DeletionHistory n M)
    (D : Finset (Fin n)) : ∃ t, ¬candidateSurvives (H.state t) D := by
  refine ⟨M, ?_⟩
  simp [H.capped, candidateSurvives]

noncomputable def DeletionHistory.stop {n M : ℕ} (H : DeletionHistory n M)
    (D : Finset (Fin n)) : ℕ := Nat.find (H.failure_exists D)

theorem DeletionHistory.stop_le_cap {n M : ℕ} (H : DeletionHistory n M)
    (D : Finset (Fin n)) : H.stop D ≤ M :=
  Nat.find_min' _ (by simp [H.capped, candidateSurvives])

theorem DeletionHistory.before_stop_iff {n M t : ℕ} (H : DeletionHistory n M)
    (D : Finset (Fin n)) : t < H.stop D ↔ candidateSurvives (H.state t) D := by
  constructor
  · intro ht
    exact Classical.not_not.mp (Nat.find_min (H.failure_exists D) ht)
  · intro ht
    by_contra hn
    have hf : ¬candidateSurvives (H.state (H.stop D)) D :=
      Nat.find_spec (H.failure_exists D)
    exact hf (candidateSurvives_subset (H.antitone (Nat.le_of_not_gt hn)) ht)

theorem DeletionHistory.stop_mono {n M : ℕ} (H : DeletionHistory n M) :
    Monotone H.stop := by
  intro D E hDE
  by_contra hn
  have hd := (H.before_stop_iff D).mp (Nat.lt_of_not_ge hn)
  have he := candidateSurvives_mono (H.closed (H.stop E)) hDE hd
  exact Nat.find_spec (H.failure_exists E) he

noncomputable def DeletionHistory.realStop {n M : ℕ} (H : DeletionHistory n M)
    (D : Finset (Fin n)) : ℝ := H.stop D

theorem DeletionHistory.realStop_mono {n M : ℕ} (H : DeletionHistory n M) :
    Monotone H.realStop := by
  intro D E hDE
  change (H.stop D : ℝ) ≤ H.stop E
  exact_mod_cast H.stop_mono hDE

theorem DeletionHistory.survival_le_best {n M t r : ℕ}
    (H : DeletionHistory n M) {D : Finset (Fin n)} (hD : D.card ≤ r)
    (hs : candidateSurvives (H.state t) D) :
    (t : ℝ) < bestDeletionTime H.realStop r := by
  have ht : (t : ℝ) < H.realStop D := by
    change (t : ℝ) < H.stop D
    exact_mod_cast (H.before_stop_iff D).mpr hs
  apply ht.trans_le
  exact Finset.le_sup' _ (by simp [allowedDeletions, hD])

end FixedClauseThreshold.Computability

end OAI
