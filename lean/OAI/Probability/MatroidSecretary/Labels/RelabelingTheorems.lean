import OAI.Probability.MatroidSecretary.Labels.RelabelingModel
import OAI.Probability.MatroidProphet.Main
import Mathlib.Combinatorics.Matroid.Loop

namespace OAI

/-! Exact transport from arbitrary finite labels to the `Fin n` information model. -/

namespace MatroidProphet.Relabeling

open Finset MeasureTheory

variable {α β : Type*}

lemma sum_le_finiteOptimum [Fintype α] (M : Matroid α) (w : α → ℝ)
    (I : Finset α) (hI : M.Indep (I : Set α)) :
    (∑ a ∈ I, w a) ≤ finiteOptimum M w := by
  classical
  have h := Finset.le_sup' (s := (Finset.univ : Finset (Finset α)))
    (f := fun J => if M.Indep (J : Set α) then ∑ a ∈ J, w a else 0)
    (Finset.mem_univ I)
  simpa only [finiteOptimum, ite_eq_left hI] using h

lemma finiteOptimum_nonneg [Fintype α] (M : Matroid α) (w : α → ℝ) :
    0 ≤ finiteOptimum M w := by
  simpa using sum_le_finiteOptimum M w ∅ (by simp)

lemma finiteOptimum_le [Fintype α] (M : Matroid α) (w : α → ℝ) {z : ℝ}
    (hz : 0 ≤ z) (h : ∀ I : Finset α, M.Indep (I : Set α) → (∑ a ∈ I, w a) ≤ z) :
    finiteOptimum M w ≤ z := by
  classical
  apply Finset.sup'_le
  intro I _
  split_ifs with hI
  · exact h I hI
  · exact hz

/-- Changing finite labels preserves the exact offline optimum, for arbitrary real weights. -/
theorem finiteOptimum_mapEquiv [Fintype α] [Fintype β]
    (M : Matroid α) (e : α ≃ β) (w : α → ℝ) :
    finiteOptimum (M.mapEquiv e) (encodeWeights e w) = finiteOptimum M w := by
  classical
  apply le_antisymm
  · apply finiteOptimum_le _ _ (finiteOptimum_nonneg M w)
    intro J hJ
    have hI : M.Indep ((J.map e.symm.toEmbedding : Finset α) : Set α) := by
      simpa using (Matroid.mapEquiv_indep_iff.mp hJ)
    simpa [encodeWeights] using sum_le_finiteOptimum M w (J.map e.symm.toEmbedding) hI
  · apply finiteOptimum_le _ _ (finiteOptimum_nonneg _ _)
    intro I hI
    have hJ : (M.mapEquiv e).Indep ((I.map e.toEmbedding : Finset β) : Set β) := by
      simpa using hI
    simpa [encodeWeights] using
      sum_le_finiteOptimum (M.mapEquiv e) (encodeWeights e w) (I.map e.toEmbedding) hJ

@[simp] theorem finiteOptimum_fin {n : ℕ} (M : Matroid (Fin n)) (w : Weights n) :
    finiteOptimum M w = optimum M w := rfl

@[simp] theorem encodeWeights_nonnegative_iff (e : α ≃ β) (w : α → ℝ) :
    (∀ b, 0 ≤ encodeWeights e w b) ↔ (∀ a, 0 ≤ w a) := by
  constructor
  · intro h a
    simpa [encodeWeights] using h (e a)
  · intro h b
    exact h (e.symm b)

@[simp] theorem mapEquiv_ground_univ (M : Matroid α) (e : α ≃ β)
    (hE : M.E = Set.univ) : (M.mapEquiv e).E = Set.univ := by
  simp [hE]

@[simp] theorem mapEquiv_loop_iff (M : Matroid α) (e : α ≃ β) (a : α) :
    (M.mapEquiv e).IsLoop (e a) ↔ M.IsLoop a := by
  exact Matroid.mapEmbedding_isLoop_iff

/-- Every finite labeled matroid has a full-ground `Fin n` representative with
exactly the original offline benchmark and all loop labels retained. -/
theorem exists_fin_representation [Fintype α] (M : Matroid α) (hE : M.E = Set.univ) :
    ∃ (e : α ≃ Fin (Fintype.card α)),
      (M.mapEquiv e).E = Set.univ ∧
      (∀ w : α → ℝ, optimum (M.mapEquiv e) (encodeWeights e w) = finiteOptimum M w) ∧
      (∀ a, (M.mapEquiv e).IsLoop (e a) ↔ M.IsLoop a) := by
  refine ⟨Fintype.equivFin α, mapEquiv_ground_univ M _ hE, ?_, ?_⟩
  · intro w
    exact finiteOptimum_mapEquiv M _ w
  · intro a
    exact mapEquiv_loop_iff M _ a

/-- Coordinate reindexing is Borel, with no regularity assumption on weights. -/
theorem measurable_encodeWeights (e : α ≃ β) : Measurable (encodeWeights e) := by
  apply Measurable.of_eval
  intro b
  exact measurable_pi_apply (e.symm b)

theorem measurable_encodeHistory [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] {n : ℕ} (e : α ≃ Fin n) (k : Fin n) :
    Measurable (encodeHistory e k) := by
  apply Measurable.of_eval
  intro j
  exact ((measurable_of_finite e).comp (measurable_fst.comp (measurable_pi_apply j))).prodMk
    (measurable_snd.comp (measurable_pi_apply j))

/-- The transported rule is measurable in precisely its permissible inputs. -/
theorem measurable_transportedDecision [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] {n bits : ℕ} (e : α ≃ Fin n)
    (A : OnlineRule n bits) (k : Fin n) :
    Measurable (fun x : Seed bits × ((α → ℝ) × LabeledHistory α k) =>
      transportedDecision e A k x.1 x.2.1 x.2.2) := by
  exact (A.measurable_decide k).comp
    (measurable_fst.prodMk (((measurable_encodeWeights e).comp
      (measurable_fst.comp measurable_snd)).prodMk
        ((measurable_encodeHistory e k).comp (measurable_snd.comp measurable_snd))))

@[simp] theorem encodeHistory_labeledHistory {n : ℕ} (e : α ≃ Fin n)
    (w : α → ℝ) (π : LabeledOrder α n) (k : Fin n) :
    encodeHistory e k (labeledHistory w π k) =
      history (encodeWeights e w) (π.trans e) k := by
  funext j
  simp [encodeHistory, labeledHistory, history, encodeWeights]

theorem transportedDecision_eq_decisionAt {n bits : ℕ} (e : α ≃ Fin n)
    (A : OnlineRule n bits) (r : Seed bits) (s v : α → ℝ)
    (π : LabeledOrder α n) (k : Fin n) :
    transportedDecision e A k r s (labeledHistory v π k) =
      decisionAt A r (encodeWeights e s) (encodeWeights e v) (π.trans e) k := by
  simp only [transportedDecision, encodeHistory_labeledHistory, decisionAt]

/-- Exact accepted-set equality holds at every prefix, not just at termination. -/
theorem transportedAcceptedThrough_eq_map [Fintype α] {n bits : ℕ}
    (e : α ≃ Fin n) (A : OnlineRule n bits) (r : Seed bits)
    (s v : α → ℝ) (π : LabeledOrder α n) (t : ℕ) :
    transportedAcceptedThrough e A r s v π t =
      (acceptedThrough A r (encodeWeights e s) (encodeWeights e v)
        (π.trans e) t).map e.symm.toEmbedding := by
  classical
  ext a
  rw [Finset.mem_map_equiv]
  simp only [transportedAcceptedThrough, acceptedThrough, Finset.mem_filter,
    Finset.mem_univ, true_and]
  simp only [transportedDecision_eq_decisionAt, Equiv.symm_symm,
    Equiv.symm_trans_apply, Equiv.symm_apply_apply]

/-- The cardinal relabeling preserves the actual sum of accepted weights exactly. -/
theorem transportedReward_eq_reward [Fintype α] {n bits : ℕ}
    (e : α ≃ Fin n) (A : OnlineRule n bits) (r : Seed bits)
    (s v : α → ℝ) (π : LabeledOrder α n) :
    transportedReward e A r s v π =
      reward A r (encodeWeights e s) (encodeWeights e v) (π.trans e) := by
  simp [transportedReward, transportedAcceptedThrough_eq_map, reward, accepted, encodeWeights]

/-- Every-prefix feasibility transfers without dropping loops or exceptional inputs. -/
theorem transported_feasible [Fintype α] {n bits : ℕ}
    (M : Matroid α) (e : α ≃ Fin n) (A : OnlineRule n bits)
    (hA : Feasible (M.mapEquiv e) A) (r : Seed bits)
    (s v : α → ℝ) (π : LabeledOrder α n) (t : ℕ)
    (hs : ∀ a, 0 ≤ s a) (hv : ∀ a, 0 ≤ v a) :
    M.Indep (transportedAcceptedThrough e A r s v π t : Set α) := by
  have hi := hA r (encodeWeights e s) (encodeWeights e v) (π.trans e) t
    ((encodeWeights_nonnegative_iff e s).2 hs) ((encodeWeights_nonnegative_iff e v).2 hv)
  simpa only [transportedAcceptedThrough_eq_map, Finset.coe_map, Equiv.coe_toEmbedding]
    using Matroid.mapEquiv_indep_iff.mp hi

/-- The relabeled implementation retains every previous acceptance irrevocably. -/
theorem transportedAcceptedThrough_mono [Fintype α] {n bits : ℕ}
    (e : α ≃ Fin n) (A : OnlineRule n bits) (r : Seed bits)
    (s v : α → ℝ) (π : LabeledOrder α n) {t t' : ℕ} (htt' : t ≤ t') :
    transportedAcceptedThrough e A r s v π t ⊆
      transportedAcceptedThrough e A r s v π t' := by
  rw [transportedAcceptedThrough_eq_map, transportedAcceptedThrough_eq_map]
  exact Finset.map_subset_map.mpr (acceptedThrough_mono A r _ _ _ htt')

end MatroidProphet.Relabeling

end OAI
