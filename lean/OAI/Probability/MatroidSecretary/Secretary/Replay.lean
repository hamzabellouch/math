import OAI.Probability.MatroidProphet.Main

namespace OAI

/-!
# Deterministic virtual-prefix replay for the secretary transport

The prefix is observed and rejected, but its history is retained when the hidden
rule is run on the suffix.  The following lemmas are pointwise in the *complete*
seed and order; no independence of the suffix order is assumed.

Source: `sections/secretary.tex`, the paragraph beginning "Initialize the
hidden-weight rule".  These are supporting transport lemmas, not a proof of the
random-prefix law or of the complete secretary endpoint.
-/

namespace MatroidProphet.SecretaryReplay

open MeasureTheory

/-- Labels in the first `K` positions of an arrival order.  This also handles
`K = 0` and `K ≥ n` without a special convention. -/
def prefixSet {n : ℕ} (π : ArrivalOrder n) (K : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun e => (π.symm e).val < K

@[simp] theorem mem_prefixSet {n : ℕ} (π : ArrivalOrder n) (K : ℕ) (e : Fin n) :
    e ∈ prefixSet π K ↔ (π.symm e).val < K := by
  simp [prefixSet]

/-- Replay every observed arrival in the core history, while forcibly rejecting
all positions strictly before `K`.  At suffix arrivals the complete *past*
history (including the rejected prefix) is supplied, never a future weight. -/
noncomputable def prefixReplay {n bits : ℕ} (A : HiddenRule n bits) (K : ℕ) :
    OnlineRule n bits where
  decide k r s h := if k.val < K then false else (sampleSimulation A).decide k r s h
  measurable_decide k := by
    by_cases hk : k.val < K
    · simp only [hk, ite_true]
      exact measurable_const
    · simp only [hk, ite_false]
      exact (sampleSimulation A).measurable_decide k

/-- Prefix rejection removes exactly the prefix labels from the simulated run. -/
theorem acceptedThrough_prefixReplay {n bits : ℕ} (A : HiddenRule n bits) (K : ℕ)
    (r : Seed bits) (s v : Weights n) (π : ArrivalOrder n) (t : ℕ) :
    acceptedThrough (prefixReplay A K) r s v π t =
      acceptedThrough (sampleSimulation A) r s v π t \ prefixSet π K := by
  classical
  ext e
  simp only [acceptedThrough, Finset.mem_sdiff, mem_prefixSet, Finset.mem_filter,
    Finset.mem_univ, true_and]
  by_cases hk : (π.symm e).val < K
  · simp [decisionAt, prefixReplay, hk]
  · simp [decisionAt, prefixReplay, hk]

/-- If the observed prefix is sacrificed by the hidden rule, explicit prefix
rejection changes no accepted label, at any arrival prefix. -/
theorem acceptedThrough_eq_hidden {n bits : ℕ} (A : HiddenRule n bits) (K : ℕ)
    (r : Seed bits) (s v : Weights n) (π : ArrivalOrder n) (t : ℕ)
    (hprefix : prefixSet π K ⊆ A.mask r) :
    acceptedThrough (prefixReplay A K) r s v π t =
      hiddenAcceptedThrough A r (glue (A.mask r) s v) π t := by
  classical
  rw [acceptedThrough_prefixReplay, sampleSimulation_acceptedThrough]
  ext e
  simp only [Finset.mem_sdiff]
  constructor
  · exact fun h => h.1
  · intro he
    refine ⟨he, ?_⟩
    intro hp
    exact (Finset.mem_sdiff.mp he).2 (hprefix hp)

/-- Only agreement on the revealed mask is required of the initial observation. -/
theorem glue_eq_of_agrees {n bits : ℕ} (A : HiddenRule n bits) (r : Seed bits)
    (s w : Weights n) (hobs : ∀ e ∈ A.mask r, s e = w e) :
    glue (A.mask r) s w = w := by
  classical
  funext e
  by_cases he : e ∈ A.mask r
  · simp [glue, he, hobs e he]
  · simp [glue, he]

/-- Exact virtual replay, with equality at every prefix, not just equal reward. -/
theorem fixedVector_acceptedThrough {n bits : ℕ} (A : HiddenRule n bits) (K : ℕ)
    (r : Seed bits) (s w : Weights n) (π : ArrivalOrder n) (t : ℕ)
    (hprefix : prefixSet π K ⊆ A.mask r)
    (hobs : ∀ e ∈ A.mask r, s e = w e) :
    acceptedThrough (prefixReplay A K) r s w π t =
      hiddenAcceptedThrough A r w π t := by
  rw [acceptedThrough_eq_hidden A K r s w π t hprefix,
    glue_eq_of_agrees A r s w hobs]

/-- The replay accepts nothing during the observation period. -/
theorem prefix_rejected {n bits : ℕ} (A : HiddenRule n bits) (K : ℕ)
    (r : Seed bits) (s v : Weights n) (π : ArrivalOrder n) {t : ℕ} (ht : t ≤ K) :
    acceptedThrough (prefixReplay A K) r s v π t = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  rw [acceptedThrough_prefixReplay] at he
  have ha := acceptedThrough_arrived (sampleSimulation A) r s v π t e
    (Finset.mem_sdiff.mp he).1
  exact (Finset.mem_sdiff.mp he).2 ((mem_prefixSet π K e).mpr (ha.trans_le ht))

/-- All actual accepted weights equal their hidden-run weights. -/
theorem fixedVector_reward {n bits : ℕ} (A : HiddenRule n bits) (K : ℕ)
    (r : Seed bits) (s w : Weights n) (π : ArrivalOrder n)
    (hprefix : prefixSet π K ⊆ A.mask r)
    (hobs : ∀ e ∈ A.mask r, s e = w e) :
    reward (prefixReplay A K) r s w π = hiddenReward A r w π := by
  unfold reward accepted hiddenReward
  rw [fixedVector_acceptedThrough A K r s w π n hprefix hobs]

/-- Pointwise domination holds even when the order depends on extra visible
secretary randomness beyond the reconstructed source seed. -/
theorem worstReward_le_replay {n bits : ℕ} (A : HiddenRule n bits) (K : ℕ)
    (r : Seed bits) (s w : Weights n) (π : ArrivalOrder n)
    (hprefix : prefixSet π K ⊆ A.mask r)
    (hobs : ∀ e ∈ A.mask r, s e = w e) :
    hiddenWorstReward A w r ≤ reward (prefixReplay A K) r s w π := by
  rw [fixedVector_reward A K r s w π hprefix hobs]
  exact hiddenWorstReward_le A w r π

/-- Pointwise feasibility of the source rule transfers at every replay prefix. -/
theorem fixedVector_feasible {n bits : ℕ} (M : Matroid (Fin n))
    (A : HiddenRule n bits) (K : ℕ)
    (hA : ∀ (w : Weights n), (∀ e, 0 ≤ w e) →
      ∀ (r : Seed bits) (π : ArrivalOrder n) (t : ℕ),
        M.Indep (hiddenAcceptedThrough A r w π t : Set (Fin n)))
    (r : Seed bits) (s w : Weights n) (π : ArrivalOrder n) (t : ℕ)
    (hw : ∀ e, 0 ≤ w e)
    (hprefix : prefixSet π K ⊆ A.mask r)
    (hobs : ∀ e ∈ A.mask r, s e = w e) :
    M.Indep (acceptedThrough (prefixReplay A K) r s w π t : Set (Fin n)) := by
  rw [fixedVector_acceptedThrough A K r s w π t hprefix hobs]
  exact hA w hw r π t

end MatroidProphet.SecretaryReplay

end OAI
