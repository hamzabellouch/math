import OAI.Probability.MatroidProphet.Algorithm.Feasible
import OAI.Probability.MatroidProphet.Maximum.Guarantee
import OAI.Probability.MatroidProphet.Priority
import OAI.Probability.MatroidProphet.Simulation

namespace OAI

namespace MatroidProphet

open MeasureTheory

noncomputable def branchOnlineRule {n bits : ℕ} (branch : Seed bits → Bool)
    (A B : OnlineRule n bits) : OnlineRule n bits where
  decide k r s h := if branch r then A.decide k r s h else B.decide k r s h
  measurable_decide k := by
    have hb : Measurable (fun x : Seed bits × (Weights n × History n k) => branch x.1) :=
      (measurable_of_countable branch).comp measurable_fst
    exact Measurable.ite (hb (measurableSet_singleton true))
      (A.measurable_decide k) (B.measurable_decide k)

noncomputable def branchHiddenRule {n bits : ℕ} (branch : Seed bits → Bool)
    (A B : HiddenRule n bits) : HiddenRule n bits where
  mask r := if branch r then A.mask r else B.mask r
  core := branchOnlineRule branch A.core B.core

lemma branchOnlineRule_acceptedThrough {n bits : ℕ} (branch : Seed bits → Bool)
    (A B : OnlineRule n bits) (r : Seed bits) (s v : Weights n) (π : ArrivalOrder n) (t : ℕ) :
    acceptedThrough (branchOnlineRule branch A B) r s v π t =
      if branch r then acceptedThrough A r s v π t else acceptedThrough B r s v π t := by
  classical
  cases hb : branch r <;> simp [acceptedThrough, decisionAt, branchOnlineRule, hb] <;> rfl

lemma branchHiddenRule_observed {n bits : ℕ} (branch : Seed bits → Bool)
    (A B : HiddenRule n bits) (r : Seed bits) (w : Weights n) :
    observed (branchHiddenRule branch A B) r w =
      if branch r then observed A r w else observed B r w := by
  funext e
  cases hb : branch r <;> simp only [observed, branchHiddenRule, hb, Bool.false_eq_true,
    ↓reduceIte]

lemma branchHiddenRule_acceptedThrough {n bits : ℕ} (branch : Seed bits → Bool)
    (A B : HiddenRule n bits) (r : Seed bits) (w : Weights n) (π : ArrivalOrder n) (t : ℕ) :
    hiddenAcceptedThrough (branchHiddenRule branch A B) r w π t =
      if branch r then hiddenAcceptedThrough A r w π t else hiddenAcceptedThrough B r w π t := by
  change acceptedThrough (branchOnlineRule branch A.core B.core) r
    (observed (branchHiddenRule branch A B) r w) w π t \ (if branch r then A.mask r else B.mask r) = _
  rw [branchHiddenRule_observed, branchOnlineRule_acceptedThrough]
  cases branch r <;> simp only [Bool.false_eq_true, ↓reduceIte, hiddenAcceptedThrough]

lemma branchHiddenRule_reward {n bits : ℕ} (branch : Seed bits → Bool)
    (A B : HiddenRule n bits) (r : Seed bits) (w : Weights n) (π : ArrivalOrder n) :
    hiddenReward (branchHiddenRule branch A B) r w π =
      if branch r then hiddenReward A r w π else hiddenReward B r w π := by
  cases hb : branch r <;> simp [hiddenReward, branchHiddenRule_acceptedThrough, hb]

lemma branchHiddenRule_worst {n bits : ℕ} (branch : Seed bits → Bool)
    (A B : HiddenRule n bits) (r : Seed bits) (w : Weights n) :
    hiddenWorstReward (branchHiddenRule branch A B) w r =
      if branch r then hiddenWorstReward A w r else hiddenWorstReward B w r := by
  classical
  cases hb : branch r <;> simp [hiddenWorstReward, branchHiddenRule_reward, hb]

instance withBotIntMeasurableSpace : MeasurableSpace (WithBot ℤ) := ⊤
instance withBotIntMeasurableSingletonClass : MeasurableSingletonClass (WithBot ℤ) :=
  ⟨fun _ => trivial⟩

noncomputable def roundedMaximumHidden {n : ℕ} (M : Matroid (Fin n))
    {bits : ℕ} (mask : Seed bits → Finset (Fin n)) : HiddenRule n bits :=
  Maximum.maximumHidden M (fun x => Priority.asLevel (roundedLevel weightBase x))
    ((measurable_of_countable Priority.asLevel).comp (measurable_roundedLevel weightBase))
    (fun a => a ≠ ⊥) mask

noncomputable def completeHiddenRule {n : ℕ} (M : Matroid (Fin n)) (hE : M.E = Set.univ) :
    HiddenRule n (mainSeedBits n) :=
  branchHiddenRule mainBranch (MainAlgorithm.hidden M hE)
    (roundedMaximumHidden M (fun r => (mainMasks r).H))

lemma branchHiddenRule_feasible {n bits : ℕ} (M : Matroid (Fin n))
    (branch : Seed bits → Bool) (A B : HiddenRule n bits)
    (hA : ∀ w, (∀ e, 0 ≤ w e) → ∀ r π t,
      M.Indep (hiddenAcceptedThrough A r w π t : Set (Fin n)))
    (hB : ∀ w, (∀ e, 0 ≤ w e) → ∀ r π t,
      M.Indep (hiddenAcceptedThrough B r w π t : Set (Fin n)))
    (w : Weights n) (hw : ∀ e, 0 ≤ w e) (r : Seed bits) (π : ArrivalOrder n) (t : ℕ) :
    M.Indep (hiddenAcceptedThrough (branchHiddenRule branch A B) r w π t : Set (Fin n)) := by
  rw [branchHiddenRule_acceptedThrough]
  cases hb : branch r
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact hB w hw r π t
  · simp only [↓reduceIte]
    exact hA w hw r π t

lemma roundedMaximumHidden_feasible {n bits : ℕ} (M : Matroid (Fin n))
    (mask : Seed bits → Finset (Fin n)) (w : Weights n) (hw : ∀ e, 0 ≤ w e)
    (r : Seed bits) (π : ArrivalOrder n) (t : ℕ) :
    M.Indep (hiddenAcceptedThrough (roundedMaximumHidden M mask) r w π t : Set (Fin n)) :=
  Maximum.maximumHidden_feasible M _ _ _ _ w hw r π t

lemma completeHiddenRule_feasible {n : ℕ} (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (w : Weights n) (hw : ∀ e, 0 ≤ w e) (r : Seed (mainSeedBits n))
    (π : ArrivalOrder n) (t : ℕ) :
    M.Indep (hiddenAcceptedThrough (completeHiddenRule M hE) r w π t : Set (Fin n)) :=
  branchHiddenRule_feasible M mainBranch _ _ (MainAlgorithm.hidden_feasible M hE)
    (roundedMaximumHidden_feasible M _) w hw r π t

end MatroidProphet

end OAI
