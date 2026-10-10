import OAI.Probability.MatroidSecretary.Labels.FiniteLabelingModel
import OAI.Probability.MatroidProphet.Main

namespace OAI

/-!
Finite-label equivalence supporting the scope statement "every finite known
labeled matroid".  No positivity, nonempty-ground, or nonloop hypothesis occurs
in the transport laws.  The proof uses mathlib's actual matroid map, not a
replacement independence predicate.
-/

namespace MatroidProphet.Labeling

open Finset

variable {E F : Type*} [Fintype E] [Fintype F]

theorem finiteOptimum_nonneg (M : Matroid E) (w : E → ℝ) :
    0 ≤ finiteOptimum M w := by
  classical
  unfold finiteOptimum
  apply Finset.le_sup'_of_le _ (Finset.mem_univ ∅)
  simp

theorem sum_le_finiteOptimum (M : Matroid E) (w : E → ℝ)
    (I : Finset E) (hI : M.Indep (I : Set E)) :
    (∑ e ∈ I, w e) ≤ finiteOptimum M w := by
  classical
  unfold finiteOptimum
  apply Finset.le_sup'_of_le _ (Finset.mem_univ I)
  simp [hI]

omit [Fintype E] [Fintype F] in
theorem mapEquiv_finset_indep (M : Matroid E) (e : E ≃ F) (I : Finset E) :
    (M.mapEquiv e).Indep (I.map e.toEmbedding : Set F) ↔ M.Indep (I : Set E) := by
  simp

theorem finiteOptimum_mapEquiv (M : Matroid E) (e : E ≃ F) (w : E → ℝ) :
    finiteOptimum (M.mapEquiv e) (fun f => w (e.symm f)) = finiteOptimum M w := by
  classical
  apply le_antisymm
  · apply Finset.sup'_le
    intro I _
    split_ifs with hI
    · have hi : M.Indep (I.map e.symm.toEmbedding : Set E) := by
        simpa using hI
      simpa using sum_le_finiteOptimum M w (I.map e.symm.toEmbedding) hi
    · exact finiteOptimum_nonneg M w
  · apply Finset.sup'_le
    intro I _
    split_ifs with hI
    · have hi := (mapEquiv_finset_indep M e I).2 hI
      simpa using sum_le_finiteOptimum (M.mapEquiv e) (fun f => w (e.symm f))
        (I.map e.toEmbedding) hi
    · exact finiteOptimum_nonneg (M.mapEquiv e) _

theorem finMatroid_ground (M : Matroid E) (hE : M.E = Set.univ) :
    (finMatroid M).E = Set.univ := by
  simp [finMatroid, hE]

theorem finWeights_nonnegative_iff (w : E → ℝ) :
    (∀ i, 0 ≤ finWeights w i) ↔ ∀ e, 0 ≤ w e := by
  constructor
  · intro h e
    simpa [finWeights] using h ((Fintype.equivFin E) e)
  · intro h i
    exact h _

theorem optimum_finMatroid (M : Matroid E) (w : E → ℝ) :
    MatroidProphet.optimum (finMatroid M) (finWeights w) = finiteOptimum M w :=
  finiteOptimum_mapEquiv M (Fintype.equivFin E) w

section Online

variable [MeasurableSpace E] [MeasurableSingletonClass E] {bits : ℕ}

/-- Conjugate an actual online rule by a fixed label enumeration.  In particular,
the translated rule does not receive a future order or a future value. -/
noncomputable def relabelRule (A : OnlineRule (Fintype.card E) bits) :
    LabeledOnlineRule E bits where
  decide k r s h := A.decide k r (finWeights s)
    (encodeHistory (Fintype.equivFin E) k h)
  measurable_decide k := by
    have hm : Measurable (fun x : Seed bits ×
        ((E → ℝ) × (Fin (k.val + 1) → E × ℝ)) =>
        (x.1, (finWeights x.2.1, encodeHistory (Fintype.equivFin E) k x.2.2))) := by
      apply Measurable.prodMk measurable_fst
      apply Measurable.prodMk
      · apply Measurable.of_eval
        intro i
        exact (measurable_pi_apply ((Fintype.equivFin E).symm i)).comp
          (measurable_fst.comp measurable_snd)
      · apply Measurable.of_eval
        intro j
        have hj : Measurable (fun x : Seed bits ×
            ((E → ℝ) × (Fin (k.val + 1) → E × ℝ)) => x.2.2 j) :=
          (measurable_pi_apply j).comp (measurable_snd.comp measurable_snd)
        exact ((measurable_of_countable (Fintype.equivFin E)).comp
          (measurable_fst.comp hj)).prodMk (measurable_snd.comp hj)
    exact (A.measurable_decide k).comp hm

omit [MeasurableSpace E] [MeasurableSingletonClass E] in
theorem encode_labeledHistory (v : E → ℝ) (π : LabeledOrder E)
    (k : Fin (Fintype.card E)) :
    encodeHistory (Fintype.equivFin E) k (labeledHistory v π k) =
      history (finWeights v) (π.trans (Fintype.equivFin E)) k := by
  funext j
  simp [encodeHistory, labeledHistory, history, finWeights]

theorem relabelRule_acceptedThrough (A : OnlineRule (Fintype.card E) bits)
    (r : Seed bits) (s v : E → ℝ) (π : LabeledOrder E) (t : ℕ) :
    (labeledAcceptedThrough (relabelRule A) r s v π t).map
      (Fintype.equivFin E).toEmbedding =
    acceptedThrough A r (finWeights s) (finWeights v)
      (π.trans (Fintype.equivFin E)) t := by
  classical
  ext index
  rw [Finset.mem_map_equiv]
  unfold labeledAcceptedThrough acceptedThrough
  rw [Finset.mem_filter, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, decisionAt, relabelRule,
    encode_labeledHistory]
  rfl

theorem relabelRule_feasible (M : Matroid E)
    (A : OnlineRule (Fintype.card E) bits) (hA : Feasible (finMatroid M) A)
    (r : Seed bits) (s v : E → ℝ) (π : LabeledOrder E) (t : ℕ)
    (hs : ∀ e, 0 ≤ s e) (hv : ∀ e, 0 ≤ v e) :
    M.Indep (labeledAcceptedThrough (relabelRule A) r s v π t : Set E) := by
  have hi := hA r (finWeights s) (finWeights v)
    (π.trans (Fintype.equivFin E)) t
    ((finWeights_nonnegative_iff s).2 hs) ((finWeights_nonnegative_iff v).2 hv)
  rw [← relabelRule_acceptedThrough A r s v π t] at hi
  exact (mapEquiv_finset_indep M (Fintype.equivFin E) _).1 hi

 

theorem relabelRule_reward (A : OnlineRule (Fintype.card E) bits)
    (r : Seed bits) (s v : E → ℝ) (π : LabeledOrder E) :
    (∑ e ∈ labeledAcceptedThrough (relabelRule A) r s v π (Fintype.card E), v e) =
      reward A r (finWeights s) (finWeights v) (π.trans (Fintype.equivFin E)) := by
  classical
  rw [reward, accepted, ← relabelRule_acceptedThrough]
  simp [finWeights]

/-- Any pointwise guarantee expressed in the actual `Fin n` model is unchanged
by transporting both the selected reward and the offline benchmark. -/
theorem relabelRule_ratio_iff (M : Matroid E)
    (A : OnlineRule (Fintype.card E) bits) (c : ℝ)
    (r : Seed bits) (s v : E → ℝ) (π : LabeledOrder E) :
    (c * finiteOptimum M v ≤
      ∑ e ∈ labeledAcceptedThrough (relabelRule A) r s v π (Fintype.card E), v e) ↔
    c * MatroidProphet.optimum (finMatroid M) (finWeights v) ≤
      reward A r (finWeights s) (finWeights v) (π.trans (Fintype.equivFin E)) := by
  rw [relabelRule_reward, optimum_finMatroid]

end Online

end MatroidProphet.Labeling

end OAI
