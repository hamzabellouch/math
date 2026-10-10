import OAI.Probability.MatroidProphet.Main

namespace OAI

/-!
# Information restrictions of the one-sample simulation

These pointwise statements make explicit the information restrictions used in
`sections/setup.tex`, Lemma `lem:simulation`: unused samples and online values
of sacrificed labels cannot affect the execution.  The final two replay
identities also support the prefix/suffix construction in `sections/secretary.tex`.
No independence, positivity, or feasibility assumptions are needed for these
deterministic identities.
-/

namespace MatroidProphet

lemma simulationObserved_eq_of_eq_on_mask {n bits : ℕ} (A : HiddenRule n bits)
    (r : Seed bits) (s s' : Weights n)
    (hs : ∀ e ∈ A.mask r, s e = s' e) :
    observed A r s = observed A r s' := by
  classical
  funext e
  by_cases he : e ∈ A.mask r
  · simp [observed, he, hs e he]
  · simp [observed, he]

lemma simulationHistory_eq_of_eq_on_mask {n bits : ℕ} (A : HiddenRule n bits)
    (r : Seed bits) (s s' : Weights n) {k : Fin n} (h : History n k)
    (hs : ∀ e ∈ A.mask r, s e = s' e) :
    simulationHistory A r s h = simulationHistory A r s' h := by
  classical
  funext j
  by_cases he : (h j).1 ∈ A.mask r
  · simp [simulationHistory, he, hs _ he]
  · simp [simulationHistory, he]

/-- The simulator's current decision ignores every sample outside its mask. -/
theorem sampleSimulation_decide_eq_of_eq_on_mask {n bits : ℕ}
    (A : HiddenRule n bits) (r : Seed bits) (s s' : Weights n)
    (k : Fin n) (h : History n k)
    (hs : ∀ e ∈ A.mask r, s e = s' e) :
    (sampleSimulation A).decide k r s h =
      (sampleSimulation A).decide k r s' h := by
  classical
  simp only [sampleSimulation]
  rw [simulationObserved_eq_of_eq_on_mask A r s s' hs,
    simulationHistory_eq_of_eq_on_mask A r s s' h hs]

lemma glue_eq_of_eq_on_regions {n : ℕ} (mask : Finset (Fin n))
    (s s' v v' : Weights n)
    (hs : ∀ e ∈ mask, s e = s' e)
    (hv : ∀ e ∉ mask, v e = v' e) :
    glue mask s v = glue mask s' v' := by
  classical
  funext e
  by_cases he : e ∈ mask
  · simp [glue, he, hs e he]
  · simp [glue, he, hv e he]

/-- Neither unused samples nor sacrificed online values change any accepted prefix. -/
theorem sampleSimulation_acceptedThrough_noninterference {n bits : ℕ}
    (A : HiddenRule n bits) (r : Seed bits) (s s' v v' : Weights n)
    (π : ArrivalOrder n) (t : ℕ)
    (hs : ∀ e ∈ A.mask r, s e = s' e)
    (hv : ∀ e ∉ A.mask r, v e = v' e) :
    acceptedThrough (sampleSimulation A) r s v π t =
      acceptedThrough (sampleSimulation A) r s' v' π t := by
  rw [sampleSimulation_acceptedThrough, sampleSimulation_acceptedThrough,
    glue_eq_of_eq_on_regions (A.mask r) s s' v v' hs hv]

/-- The same information invariance holds for the reward in actual online values. -/
theorem sampleSimulation_reward_noninterference {n bits : ℕ}
    (A : HiddenRule n bits) (r : Seed bits) (s s' v v' : Weights n)
    (π : ArrivalOrder n)
    (hs : ∀ e ∈ A.mask r, s e = s' e)
    (hv : ∀ e ∉ A.mask r, v e = v' e) :
    reward (sampleSimulation A) r s v π =
      reward (sampleSimulation A) r s' v' π := by
  rw [sampleSimulation_reward, sampleSimulation_reward,
    glue_eq_of_eq_on_regions (A.mask r) s s' v v' hs hv]

/-- A sacrificed label is rejected at every prefix, irrespective of its value. -/
theorem sampleSimulation_rejects_mask {n bits : ℕ} (A : HiddenRule n bits)
    (r : Seed bits) (s v : Weights n) (π : ArrivalOrder n) (t : ℕ)
    (e : Fin n) (he : e ∈ A.mask r) :
    e ∉ acceptedThrough (sampleSimulation A) r s v π t := by
  rw [sampleSimulation_acceptedThrough]
  exact fun h => (Finset.mem_sdiff.mp h).2 he

lemma glue_observed_left {n bits : ℕ} (A : HiddenRule n bits)
    (r : Seed bits) (w : Weights n) :
    glue (A.mask r) (observed A r w) w = w := by
  classical
  funext e
  by_cases he : e ∈ A.mask r <;> simp [glue, observed, he]

/-- Replaying the full arrived history after supplying only the observed mask
agrees exactly with the hidden rule, at every prefix including zero. -/
theorem sampleSimulation_replay_acceptedThrough {n bits : ℕ}
    (A : HiddenRule n bits) (r : Seed bits) (w : Weights n)
    (π : ArrivalOrder n) (t : ℕ) :
    acceptedThrough (sampleSimulation A) r (observed A r w) w π t =
      hiddenAcceptedThrough A r w π t := by
  rw [sampleSimulation_acceptedThrough, glue_observed_left]

/-- The replay identity preserves the actual reward without a numerical loss. -/
theorem sampleSimulation_replay_reward {n bits : ℕ}
    (A : HiddenRule n bits) (r : Seed bits) (w : Weights n)
    (π : ArrivalOrder n) :
    reward (sampleSimulation A) r (observed A r w) w π = hiddenReward A r w π := by
  rw [sampleSimulation_reward, glue_observed_left]

end MatroidProphet

end OAI
