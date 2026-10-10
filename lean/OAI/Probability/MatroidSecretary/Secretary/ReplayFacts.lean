import OAI.Probability.MatroidProphet.Main
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace OAI

/-!
# Deterministic replay for the secretary transport

This optional supplement uses a distinct namespace so it can coexist with the
canonical `SecretaryReplay` implementation without duplicate declaration names.

These lemmas concern the replay step in the proof of `cor:secretary` in the
pinned `sections/secretary.tex`. They do not assert or assume the random-prefix
law. The latter is a separate probability obligation. A reconstructed seed may
be any function of the secretary seed and observed prefix: all the results
below hold pointwise for every seed and every completed arrival permutation.
-/

namespace MatroidProphet.SecretaryReplaySupplement

open MeasureTheory

/-- Agreement on the sacrificed labels is the exact information needed to replay
an actual fixed vector. Values supplied outside that mask are irrelevant. -/
lemma glue_eq_of_agree {n : ℕ} (mask : Finset (Fin n)) (s w : Weights n)
    (hs : ∀ e ∈ mask, s e = w e) : glue mask s w = w := by
  classical
  funext e
  by_cases he : e ∈ mask
  · simp [glue, he, hs e he]
  · simp [glue, he]

lemma observed_agrees {n bits : ℕ} (A : HiddenRule n bits) (r : Seed bits)
    (w : Weights n) : ∀ e ∈ A.mask r, observed A r w e = w e := by
  classical
  intro e he
  simp [observed, he]

/-- The actual current and past label--weight pairs, including rejected prefix
arrivals, are passed to the source core unchanged. -/
lemma history_replay {n bits : ℕ} (A : HiddenRule n bits) (r : Seed bits)
    (s w : Weights n) (hs : ∀ e ∈ A.mask r, s e = w e)
    (π : ArrivalOrder n) (k : Fin n) :
    simulationHistory A r s (history w π k) = history w π k := by
  rw [simulationHistory_eq, glue_eq_of_agree _ _ _ hs]

/-- Exact accepted-set identity at every time, not just equality of total reward. -/
theorem acceptedThrough_replay {n bits : ℕ} (A : HiddenRule n bits) (r : Seed bits)
    (s w : Weights n) (hs : ∀ e ∈ A.mask r, s e = w e)
    (π : ArrivalOrder n) (t : ℕ) :
    acceptedThrough (sampleSimulation A) r s w π t =
      hiddenAcceptedThrough A r w π t := by
  rw [sampleSimulation_acceptedThrough, glue_eq_of_agree _ _ _ hs]

/-- Replay never replaces a realized payoff by a sampled or auxiliary value. -/
theorem reward_replay {n bits : ℕ} (A : HiddenRule n bits) (r : Seed bits)
    (s w : Weights n) (hs : ∀ e ∈ A.mask r, s e = w e)
    (π : ArrivalOrder n) :
    reward (sampleSimulation A) r s w π = hiddenReward A r w π := by
  rw [sampleSimulation_reward, glue_eq_of_agree _ _ _ hs]

/-- Only the revealed vector is needed for the initial observation. -/
theorem observed_replay {n bits : ℕ} (A : HiddenRule n bits) (r : Seed bits)
    (w : Weights n) (π : ArrivalOrder n) (t : ℕ) :
    acceptedThrough (sampleSimulation A) r (observed A r w) w π t =
      hiddenAcceptedThrough A r w π t :=
  acceptedThrough_replay A r _ w (observed_agrees A r w) π t

/-- If the mask is exactly the observed prefix set, no prefix label is accepted.
The bound includes both zero-length and full-length prefixes. -/
theorem prefix_rejected {n bits : ℕ} (A : HiddenRule n bits) (r : Seed bits)
    (s w : Weights n) (π : ArrivalOrder n) (K : ℕ)
    (hmask : ∀ e, e ∈ A.mask r ↔ (π.symm e).val < K) :
    acceptedThrough (sampleSimulation A) r s w π K = ∅ := by
  classical
  rw [sampleSimulation_acceptedThrough]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨he, hnot⟩ := Finset.mem_sdiff.mp he
  exact hnot ((hmask e).mpr (acceptedThrough_arrived _ _ _ _ _ _ _ he))

/-- The prefix is still excluded at all later times. -/
theorem accepted_after_prefix {n bits : ℕ} (A : HiddenRule n bits) (r : Seed bits)
    (s w : Weights n) (π : ArrivalOrder n) (K t : ℕ)
    (hmask : ∀ e, e ∈ A.mask r ↔ (π.symm e).val < K)
    {e : Fin n} (he : e ∈ acceptedThrough (sampleSimulation A) r s w π t) :
    K ≤ (π.symm e).val := by
  classical
  rw [sampleSimulation_acceptedThrough] at he
  exact Nat.le_of_not_gt (fun h => (Finset.mem_sdiff.mp he).2 ((hmask e).mpr h))

/-- An arbitrary suffix order, even one knowing all unused seed coordinates,
cannot defeat the pointwise minimum over completed permutations. -/
theorem worstReward_le_replay {n bits : ℕ} (A : HiddenRule n bits) (r : Seed bits)
    (s w : Weights n) (hs : ∀ e ∈ A.mask r, s e = w e)
    (π : ArrivalOrder n) :
    hiddenWorstReward A w r ≤ reward (sampleSimulation A) r s w π := by
  rw [reward_replay A r s w hs π]
  exact hiddenWorstReward_le A w r π

/-- Every-prefix matroid feasibility transfers without a condition on the
suffix adversary or on weights assigned outside the observation mask. -/
theorem feasible_replay {n bits : ℕ} (M : Matroid (Fin n)) (A : HiddenRule n bits)
    (hA : ∀ (w : Weights n), (∀ e, 0 ≤ w e) →
      ∀ (r : Seed bits) (π : ArrivalOrder n) (t : ℕ),
        M.Indep (hiddenAcceptedThrough A r w π t : Set (Fin n)))
    (r : Seed bits) (s w : Weights n) (hw : ∀ e, 0 ≤ w e)
    (hs : ∀ e ∈ A.mask r, s e = w e) (π : ArrivalOrder n) (t : ℕ) :
    M.Indep (acceptedThrough (sampleSimulation A) r s w π t : Set (Fin n)) := by
  rw [acceptedThrough_replay A r s w hs π t]
  exact hA w hw r π t

end MatroidProphet.SecretaryReplaySupplement

end OAI
