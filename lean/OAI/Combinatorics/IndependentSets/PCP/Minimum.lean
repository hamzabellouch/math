import Mathlib
import OAI.Combinatorics.IndependentSets.PCP.ConstraintGraph

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.PCP.ConstraintGraph

variable {V E A : Type*}

section Minimum

variable [Fintype V] [Fintype E] [Fintype A] [Nonempty A]

def rejectionCounts (G : ConstraintGraph V E A) : Finset Nat := by
  classical
  exact Finset.univ.image G.rejectionCount

theorem rejectionCounts_nonempty (G : ConstraintGraph V E A) :
    G.rejectionCounts.Nonempty := by
  classical
  exact Finset.univ_nonempty.image G.rejectionCount

def minimumRejections (G : ConstraintGraph V E A) : Nat :=
  G.rejectionCounts.min' G.rejectionCounts_nonempty

theorem minimumRejections_le (G : ConstraintGraph V E A) (labeling : V → A) :
    G.minimumRejections ≤ G.rejectionCount labeling := by
  classical
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨labeling, Finset.mem_univ _, rfl⟩)

theorem exists_minimizer (G : ConstraintGraph V E A) :
    ∃ labeling : V → A, G.rejectionCount labeling = G.minimumRejections := by
  classical
  have h := Finset.min'_mem G.rejectionCounts G.rejectionCounts_nonempty
  obtain ⟨labeling, _, heq⟩ := Finset.mem_image.mp h
  exact ⟨labeling, heq⟩

theorem le_minimumRejections_iff (G : ConstraintGraph V E A) (bound : Nat) :
    bound ≤ G.minimumRejections ↔ ∀ labeling : V → A, bound ≤ G.rejectionCount labeling := by
  constructor
  · intro h labeling
    exact h.trans (G.minimumRejections_le labeling)
  · intro h
    obtain ⟨labeling, heq⟩ := G.exists_minimizer
    rw [← heq]
    exact h labeling

theorem minimumRejections_le_card (G : ConstraintGraph V E A) :
    G.minimumRejections ≤ Fintype.card E := by
  obtain ⟨labeling, heq⟩ := G.exists_minimizer
  rw [← heq]
  exact G.rejectionCount_le labeling

omit [Fintype V] [Fintype A] [Nonempty A] in
theorem rejectionCount_eq_zero_iff (G : ConstraintGraph V E A) (labeling : V → A) :
    G.rejectionCount labeling = 0 ↔ ∀ e, G.edgeSatisfied labeling e = true := by
  classical
  constructor
  · intro h e
    have hempty : G.rejectedDarts labeling = ∅ := Finset.card_eq_zero.mp h
    cases he : G.edgeSatisfied labeling e with
    | false =>
        have hm := (G.mem_rejectedDarts labeling e).mpr he
        rw [hempty] at hm
        simp at hm
    | true => rfl
  · intro h
    simp [rejectionCount, rejectedDarts, h]

theorem minimumRejections_eq_zero_iff (G : ConstraintGraph V E A) :
    G.minimumRejections = 0 ↔ G.Satisfiable := by
  constructor
  · intro h
    obtain ⟨labeling, heq⟩ := G.exists_minimizer
    exact ⟨labeling, (G.rejectionCount_eq_zero_iff labeling).mp (heq.trans h)⟩
  · rintro ⟨labeling, h⟩
    have hc := (G.rejectionCount_eq_zero_iff labeling).mpr h
    exact Nat.eq_zero_of_le_zero (hc ▸ G.minimumRejections_le labeling)

def gap (G : ConstraintGraph V E A) : ℝ :=
  (G.minimumRejections : ℝ) / Fintype.card E

theorem gap_nonnegative (G : ConstraintGraph V E A) : 0 ≤ G.gap :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem gap_le_one [Nonempty E] (G : ConstraintGraph V E A) : G.gap ≤ 1 := by
  have he : (0 : ℝ) < Fintype.card E := by exact_mod_cast Fintype.card_pos
  apply (div_le_iff₀ he).mpr
  simpa only [one_mul] using (Nat.cast_le.mpr G.minimumRejections_le_card :
    (G.minimumRejections : ℝ) ≤ (Fintype.card E : ℝ))

theorem gap_eq_zero_iff [Nonempty E] (G : ConstraintGraph V E A) :
    G.gap = 0 ↔ G.Satisfiable := by
  have he : (Fintype.card E : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [gap, div_eq_zero_iff, he, or_false, Nat.cast_eq_zero]
  exact G.minimumRejections_eq_zero_iff

theorem le_gap_iff [Nonempty E] (G : ConstraintGraph V E A) (ε : ℝ) :
    ε ≤ G.gap ↔ ∀ labeling : V → A,
      ε * Fintype.card E ≤ (G.rejectionCount labeling : ℝ) := by
  have he : (0 : ℝ) < Fintype.card E := by exact_mod_cast Fintype.card_pos
  change ε ≤ (G.minimumRejections : ℝ) / Fintype.card E ↔ _
  rw [le_div_iff₀ he]
  constructor
  · intro h labeling
    exact h.trans (Nat.cast_le.mpr (G.minimumRejections_le labeling))
  · intro h
    obtain ⟨labeling, heq⟩ := G.exists_minimizer
    simpa only [heq] using h labeling

theorem inverse_card_le_gap_of_unsatisfiable [Nonempty E]
    (G : ConstraintGraph V E A) (unsat : ¬ G.Satisfiable) :
    1 / (Fintype.card E : ℝ) ≤ G.gap := by
  apply (G.le_gap_iff _).mpr
  intro labeling
  have he : (Fintype.card E : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hc : (1 : ℝ) ≤ (G.rejectionCount labeling : ℝ) := by
    exact_mod_cast G.rejectionCount_positive unsat labeling
  simpa only [div_mul_cancel₀ _ he] using hc

end Minimum

variable {W D B : Type*}

def reindex (G : ConstraintGraph V E A) (vertices : V ≃ W) (darts : E ≃ D)
    (labels : A ≃ B) : ConstraintGraph W D B where
  reverse := darts.symm.trans (G.reverse.trans darts)
  reverse_involutive := by
    intro d
    change darts (G.reverse (darts.symm (darts (G.reverse (darts.symm d))))) = d
    rw [darts.symm_apply_apply, G.reverse_involutive, darts.apply_symm_apply]
  tail := fun d => vertices (G.tail (darts.symm d))
  accepts := fun d a b => G.accepts (darts.symm d) (labels.symm a) (labels.symm b)
  reverse_accepts := by
    intro d a b
    simpa only [Equiv.trans_apply, darts.symm_apply_apply] using
      G.reverse_accepts (darts.symm d) (labels.symm a) (labels.symm b)

def labelingEquiv (vertices : V ≃ W) (labels : A ≃ B) : (V → A) ≃ (W → B) where
  toFun := fun labeling w => labels (labeling (vertices.symm w))
  invFun := fun labeling v => labels.symm (labeling (vertices v))
  left_inv := by intro labeling; funext v; simp
  right_inv := by intro labeling; funext w; simp

theorem reindex_edgeSatisfied (G : ConstraintGraph V E A)
    (vertices : V ≃ W) (darts : E ≃ D) (labels : A ≃ B)
    (labeling : V → A) (e : E) :
    (G.reindex vertices darts labels).edgeSatisfied (labelingEquiv vertices labels labeling)
      (darts e) = G.edgeSatisfied labeling e := by
  simp [reindex, labelingEquiv, edgeSatisfied, head, Equiv.trans_apply]

theorem reindex_rejectionCount [Fintype E] [Fintype D] (G : ConstraintGraph V E A)
    (vertices : V ≃ W) (darts : E ≃ D) (labels : A ≃ B) (labeling : V → A) :
    (G.reindex vertices darts labels).rejectionCount (labelingEquiv vertices labels labeling) =
      G.rejectionCount labeling := by
  classical
  unfold rejectionCount
  symm
  apply Finset.card_bij (fun e _ => darts e)
  · intro e he
    rw [mem_rejectedDarts, reindex_edgeSatisfied]
    exact (G.mem_rejectedDarts labeling e).mp he
  · intro e _ f _ h
    exact darts.injective h
  · intro d hd
    refine ⟨darts.symm d, ?_, darts.apply_symm_apply d⟩
    rw [mem_rejectedDarts]
    rw [← reindex_edgeSatisfied G vertices darts labels labeling (darts.symm d)]
    rw [darts.apply_symm_apply]
    exact (mem_rejectedDarts _ _ _).mp hd

variable [Fintype V] [Fintype E] [Fintype A] [Nonempty A]
  [Fintype W] [Fintype D] [Fintype B] [Nonempty B]

omit [Nonempty A] [Nonempty B] in
theorem rejectionCounts_reindex (G : ConstraintGraph V E A)
    (vertices : V ≃ W) (darts : E ≃ D) (labels : A ≃ B) :
    (G.reindex vertices darts labels).rejectionCounts = G.rejectionCounts := by
  classical
  ext n
  simp only [rejectionCounts, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨labeling, hn⟩
    refine ⟨(labelingEquiv vertices labels).symm labeling, ?_⟩
    rw [← reindex_rejectionCount G vertices darts labels,
      Equiv.apply_symm_apply]
    exact hn
  · rintro ⟨labeling, hn⟩
    refine ⟨labelingEquiv vertices labels labeling, ?_⟩
    rw [reindex_rejectionCount]
    exact hn

theorem minimumRejections_reindex (G : ConstraintGraph V E A)
    (vertices : V ≃ W) (darts : E ≃ D) (labels : A ≃ B) :
    (G.reindex vertices darts labels).minimumRejections = G.minimumRejections := by
  unfold minimumRejections
  simp only [rejectionCounts_reindex]

theorem gap_reindex (G : ConstraintGraph V E A)
    (vertices : V ≃ W) (darts : E ≃ D) (labels : A ≃ B) :
    (G.reindex vertices darts labels).gap = G.gap := by
  unfold gap
  rw [minimumRejections_reindex, Fintype.card_congr darts]

theorem satisfiable_reindex (G : ConstraintGraph V E A)
    (vertices : V ≃ W) (darts : E ≃ D) (labels : A ≃ B) :
    (G.reindex vertices darts labels).Satisfiable ↔ G.Satisfiable := by
  rw [← minimumRejections_eq_zero_iff, minimumRejections_reindex,
    minimumRejections_eq_zero_iff]

end IndependentSetsGames.Foundations.PCP.ConstraintGraph

end

end OAI
