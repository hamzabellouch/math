import OAI.Probability.MatroidSecretary.Labels.LabeledHiddenModel
import OAI.Probability.MatroidSecretary.Labels.FiniteLabelTransport
import OAI.Probability.MatroidProphet.Main

namespace OAI

/-!
# The full hidden-vector endpoint on arbitrary finite labels

The enumeration is fixed before weights. These exact transport identities
preserve observation, sacrifice, every prefix, and the order minimum before
integration; they do not merely rename an expected fixed-order reward.
-/

namespace MatroidProphet.Labeling

open Finset MeasureTheory

variable {E : Type*} [Fintype E] [MeasurableSpace E]
  [MeasurableSingletonClass E] {bits : ℕ}

noncomputable def relabelHiddenRule (A : HiddenRule (Fintype.card E) bits) :
    LabeledHiddenRule E bits where
  mask r := (A.mask r).map (Fintype.equivFin E).symm.toEmbedding
  core := relabelRule A.core

theorem relabelHiddenRule_observed (A : HiddenRule (Fintype.card E) bits)
    (r : Seed bits) (w : E → ℝ) :
    finWeights (labeledObserved (relabelHiddenRule A) r w) =
      observed A r (finWeights w) := by
  classical
  funext i
  simp [finWeights, labeledObserved, relabelHiddenRule, observed]

theorem relabelHiddenRule_acceptedThrough
    (A : HiddenRule (Fintype.card E) bits) (r : Seed bits)
    (w : E → ℝ) (π : LabeledOrder E) (t : ℕ) :
    (labeledHiddenAcceptedThrough (relabelHiddenRule A) r w π t).map
        (Fintype.equivFin E).toEmbedding =
      hiddenAcceptedThrough A r (finWeights w)
        (π.trans (Fintype.equivFin E)) t := by
  classical
  unfold labeledHiddenAcceptedThrough hiddenAcceptedThrough
  rw [Finset.map_sdiff]
  change (labeledAcceptedThrough (relabelRule A.core) r
      (labeledObserved (relabelHiddenRule A) r w) w π t).map
      (Fintype.equivFin E).toEmbedding \
      ((A.mask r).map (Fintype.equivFin E).symm.toEmbedding).map
        (Fintype.equivFin E).toEmbedding = _
  rw [relabelRule_acceptedThrough, relabelHiddenRule_observed]
  congr 1
  ext i
  simp

theorem relabelHiddenRule_reward (A : HiddenRule (Fintype.card E) bits)
    (r : Seed bits) (w : E → ℝ) (π : LabeledOrder E) :
    labeledHiddenReward (relabelHiddenRule A) r w π =
      hiddenReward A r (finWeights w) (π.trans (Fintype.equivFin E)) := by
  classical
  rw [hiddenReward, ← relabelHiddenRule_acceptedThrough]
  simp [labeledHiddenReward, finWeights]

/-- The set of labeled orders is transported bijectively, so the exact
seedwise adversarial minimum, not just any one order, is preserved. -/
theorem relabelHiddenRule_worstReward (A : HiddenRule (Fintype.card E) bits)
    (w : E → ℝ) (r : Seed bits) :
    labeledHiddenWorstReward (relabelHiddenRule A) w r =
      hiddenWorstReward A (finWeights w) r := by
  classical
  apply le_antisymm
  · apply Finset.le_inf'
    intro π _
    have h := Finset.inf'_le
      (labeledHiddenReward (relabelHiddenRule A) r w)
      (Finset.mem_univ (π.trans (Fintype.equivFin E).symm))
    simpa only [labeledHiddenWorstReward, relabelHiddenRule_reward,
      Equiv.trans_assoc, Equiv.symm_trans_self, Equiv.trans_refl] using h
  · apply Finset.le_inf'
    intro π _
    rw [relabelHiddenRule_reward]
    exact Finset.inf'_le _ (Finset.mem_univ _)

theorem relabelHiddenRule_feasible (M : Matroid E)
    (A : HiddenRule (Fintype.card E) bits)
    (hA : ∀ (w : Weights (Fintype.card E)), (∀ e, 0 ≤ w e) →
      ∀ (r : Seed bits) (π : ArrivalOrder (Fintype.card E)) (t : ℕ),
        (finMatroid M).Indep (hiddenAcceptedThrough A r w π t : Set _))
    (w : E → ℝ) (hw : ∀ e, 0 ≤ w e) (r : Seed bits)
    (π : LabeledOrder E) (t : ℕ) :
    M.Indep (labeledHiddenAcceptedThrough (relabelHiddenRule A) r w π t : Set E) := by
  have hi := hA (finWeights w) ((finWeights_nonnegative_iff w).2 hw) r
    (π.trans (Fintype.equivFin E)) t
  rw [← relabelHiddenRule_acceptedThrough A r w π t] at hi
  exact (mapEquiv_finset_indep M (Fintype.equivFin E) _).1 hi

omit [MeasurableSingletonClass E] in
/-- A hidden label remains sacrificed for every order and every prefix,
irrespective of what the online core would have decided. -/
theorem labeledHiddenAcceptedThrough_disjoint_mask
    (A : LabeledHiddenRule E bits) (r : Seed bits) (w : E → ℝ)
    (π : LabeledOrder E) (t : ℕ) :
    Disjoint (labeledHiddenAcceptedThrough A r w π t) (A.mask r) := by
  classical
  exact Finset.sdiff_disjoint

/-- Literal arbitrary-finite-label version of the hidden-vector result.
All masked labels, loops, empty types, ties and zero weights are retained. -/
theorem hidden_vector_finite_labels (M : Matroid E) (hE : M.E = Set.univ) :
    ∃ (bits : ℕ) (ν : Measure (Seed bits)), IsProbabilityMeasure ν ∧
    ∃ A : LabeledHiddenRule E bits,
      (∀ (w : E → ℝ), (∀ e, 0 ≤ w e) →
        ∀ (r : Seed bits) (π : LabeledOrder E) (t : ℕ),
          M.Indep (labeledHiddenAcceptedThrough A r w π t : Set E)) ∧
      ∀ (w : E → ℝ), (∀ e, 0 ≤ w e) →
        ((2 : ℝ) ^ 293)⁻¹ * finiteOptimum M w ≤
          ∫ r, labeledHiddenWorstReward A w r ∂ν := by
  obtain ⟨bits, ν, hν, A, hA, hbound⟩ :=
    MatroidProphet.hidden_vector (Fintype.card E) (finMatroid M)
      (finMatroid_ground M hE)
  refine ⟨bits, ν, hν, relabelHiddenRule A, relabelHiddenRule_feasible M A hA, ?_⟩
  intro w hw
  have h := hbound (finWeights w) ((finWeights_nonnegative_iff w).2 hw)
  simpa only [← relabelHiddenRule_worstReward, optimum_finMatroid] using h

end MatroidProphet.Labeling

end OAI
