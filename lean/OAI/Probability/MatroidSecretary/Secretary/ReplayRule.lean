import OAI.Probability.MatroidSecretary.Secretary.Model
import OAI.Probability.MatroidSecretary.Secretary.Observation
import OAI.Probability.MatroidSecretary.Secretary.Replay

namespace OAI

/-!
# The actual history-only secretary rule reconstructed from a complete initial seed

The decoder consumes only the initial seed and the label set of the already
observed prefix. The observation vector is extracted from actual past arrivals.
A total mask-consistency guard rejects on unsupported decoder outcomes, ensuring
feasibility for every initial seed rather than merely almost surely.
-/

namespace MatroidProphet.SecretaryReplay

open MeasureTheory

/-- A concrete secretary rule from a hidden rule and a precommitted decoder.
The seed type is finite, but its law is arbitrary and need not be uniform. -/
noncomputable def reconstructedRule {n bits : ℕ} {Q : Type*}
    [Fintype Q] [MeasurableSpace Q] [MeasurableSingletonClass Q]
    (A : HiddenRule n bits) (K : Q → Fin (n + 1))
    (decode : Q → Finset (Fin n) → Seed bits) : SecretaryRule n Q where
  prefixLength := K
  measurable_prefixLength := measurable_of_finite K
  decide k q h :=
    let P := prefixLabels (K q).val h
    let r := decode q P
    if A.mask r = P then A.core.decide k r (prefixWeights (K q).val h) h else false
  measurable_decide k := by
    classical
    apply measurable_from_prod_countable_right
    intro q
    have hp := measurable_prefixLabels k (K q).val
    have hr : Measurable (fun h : History n k => decode q (prefixLabels (K q).val h)) :=
      (measurable_of_finite (decode q)).comp hp
    have hs : MeasurableSet {z : Seed bits × Finset (Fin n) | A.mask z.1 = z.2} :=
      (Set.toFinite _).measurableSet
    have hm : MeasurableSet {h : History n k |
        A.mask (decode q (prefixLabels (K q).val h)) = prefixLabels (K q).val h} :=
      (hr.prodMk hp) hs
    exact Measurable.ite hm
      ((A.core.measurable_decide k).comp
        (hr.prodMk ((measurable_prefixWeights k (K q).val).prodMk measurable_id)))
      measurable_const

/-- Once the prefix is complete, the decoder sees its full label set; no suffix
label changes the reconstructed seed. -/
theorem decoder_history {n bits : ℕ} {Q : Type*}
    (K : Q → Fin (n + 1)) (decode : Q → Finset (Fin n) → Seed bits)
    (q : Q) (w : Weights n) (π : ArrivalOrder n) (k : Fin n)
    (hk : (K q).val ≤ k.val) :
    decode q (prefixLabels (K q).val (history w π k)) =
      decode q (orderPrefix π (K q).val) := by
  rw [prefixLabels_history w π k (K q).val (hk.trans (Nat.le_succ _))]

/-- On mask-consistent outcomes the actual no-sample secretary execution exactly
replays the hidden rule at every prefix. -/
theorem reconstructed_acceptedThrough {n bits : ℕ} {Q : Type*}
    [Fintype Q] [MeasurableSpace Q] [MeasurableSingletonClass Q]
    (A : HiddenRule n bits) (K : Q → Fin (n + 1))
    (decode : Q → Finset (Fin n) → Seed bits)
    (q : Q) (w : Weights n) (π : ArrivalOrder n) (t : ℕ)
    (hmask : A.mask (decode q (orderPrefix π (K q).val)) = orderPrefix π (K q).val) :
    secretaryAcceptedThrough (reconstructedRule A K decode) q w π t =
      hiddenAcceptedThrough A (decode q (orderPrefix π (K q).val)) w π t := by
  classical
  ext e
  by_cases hk : (π.symm e).val < (K q).val
  · have he : e ∈ A.mask (decode q (orderPrefix π (K q).val)) := by
      rw [hmask, mem_orderPrefix]
      exact hk
    simp [secretaryAcceptedThrough, secretaryDecisionAt, reconstructedRule, hk,
      hiddenAcceptedThrough, he]
  · have hle : (K q).val ≤ (π.symm e).val := Nat.le_of_not_gt hk
    have hp := prefixLabels_history w π (π.symm e) (K q).val (hle.trans (Nat.le_succ _))
    have ho := prefixWeights_eq_observed A (decode q (orderPrefix π (K q).val))
      w π (π.symm e) (K q).val (hle.trans (Nat.le_succ _)) hmask
    have he : e ∉ A.mask (decode q (orderPrefix π (K q).val)) := by
      rw [hmask, mem_orderPrefix]
      exact hk
    simp only [secretaryAcceptedThrough, hiddenAcceptedThrough, acceptedThrough,
      Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and, he,
      not_false_eq_true, and_true]
    simp [secretaryDecisionAt, reconstructedRule, hk, hp, hmask, ho, decisionAt]

/-- On an unsupported decoder outcome the total construction accepts nothing. -/
theorem reconstructed_acceptedThrough_of_mismatch {n bits : ℕ} {Q : Type*}
    [Fintype Q] [MeasurableSpace Q] [MeasurableSingletonClass Q]
    (A : HiddenRule n bits) (K : Q → Fin (n + 1))
    (decode : Q → Finset (Fin n) → Seed bits)
    (q : Q) (w : Weights n) (π : ArrivalOrder n) (t : ℕ)
    (hmask : A.mask (decode q (orderPrefix π (K q).val)) ≠ orderPrefix π (K q).val) :
    secretaryAcceptedThrough (reconstructedRule A K decode) q w π t = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e
  by_cases hk : (π.symm e).val < (K q).val
  · simp [secretaryAcceptedThrough, secretaryDecisionAt, reconstructedRule, hk]
  · have hle : (K q).val ≤ (π.symm e).val := Nat.le_of_not_gt hk
    have hp := prefixLabels_history w π (π.symm e) (K q).val (hle.trans (Nat.le_succ _))
    simp [secretaryAcceptedThrough, secretaryDecisionAt, reconstructedRule, hp, hmask]

/-- Feasibility is pointwise for every complete initial seed, including null
outcomes of the conditional reconstruction kernels. -/
theorem reconstructed_feasible {n bits : ℕ} {Q : Type*}
    [Fintype Q] [MeasurableSpace Q] [MeasurableSingletonClass Q]
    (M : Matroid (Fin n)) (A : HiddenRule n bits)
    (K : Q → Fin (n + 1)) (decode : Q → Finset (Fin n) → Seed bits)
    (hA : ∀ (w : Weights n), (∀ e, 0 ≤ w e) →
      ∀ (r : Seed bits) (π : ArrivalOrder n) (t : ℕ),
        M.Indep (hiddenAcceptedThrough A r w π t : Set (Fin n))) :
    SecretaryFeasible M (reconstructedRule A K decode) := by
  intro q w hw π t
  by_cases hm : A.mask (decode q (orderPrefix π (K q).val)) = orderPrefix π (K q).val
  · rw [reconstructed_acceptedThrough A K decode q w π t hm]
    exact hA w hw _ π t
  · rw [reconstructed_acceptedThrough_of_mismatch A K decode q w π t hm]
    simp

/-- Exact replay includes reward, with the actual fixed vector on every accept. -/
theorem reconstructed_reward {n bits : ℕ} {Q : Type*}
    [Fintype Q] [MeasurableSpace Q] [MeasurableSingletonClass Q]
    (A : HiddenRule n bits) (K : Q → Fin (n + 1))
    (decode : Q → Finset (Fin n) → Seed bits)
    (q : Q) (w : Weights n) (π : ArrivalOrder n)
    (hmask : A.mask (decode q (orderPrefix π (K q).val)) = orderPrefix π (K q).val) :
    secretaryReward (reconstructedRule A K decode) q w π =
      hiddenReward A (decode q (orderPrefix π (K q).val)) w π := by
  unfold secretaryReward hiddenReward
  rw [reconstructed_acceptedThrough A K decode q w π n hmask]

/-- The pointwise comparison permits arbitrary full-seed-aware suffix orders. -/
theorem worstReward_le_reconstructed {n bits : ℕ} {Q : Type*}
    [Fintype Q] [MeasurableSpace Q] [MeasurableSingletonClass Q]
    (A : HiddenRule n bits) (K : Q → Fin (n + 1))
    (decode : Q → Finset (Fin n) → Seed bits)
    (q : Q) (w : Weights n) (π : ArrivalOrder n)
    (hmask : A.mask (decode q (orderPrefix π (K q).val)) = orderPrefix π (K q).val) :
    hiddenWorstReward A w (decode q (orderPrefix π (K q).val)) ≤
      secretaryReward (reconstructedRule A K decode) q w π := by
  rw [reconstructed_reward A K decode q w π hmask]
  exact hiddenWorstReward_le A w _ π

end MatroidProphet.SecretaryReplay

end OAI
