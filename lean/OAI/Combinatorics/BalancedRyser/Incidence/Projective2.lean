import Mathlib
import OAI.Combinatorics.BalancedRyser.Incidence.Projective

namespace OAI

namespace Balanced
open scoped _root_.Balanced

variable {F : Type*} [Field F]

@[simp] theorem dualPoint_dualLine (P : ProjectivePoint F) :
    dualPoint (dualLine P) = P := by
  cases P with
  | inl p => rcases p with ⟨x,y⟩; simp [dualLine, dualPoint]
  | inr d => cases d <;> rfl

@[simp] theorem dualLine_dualPoint (l : ProjectiveLine F) :
    dualLine (dualPoint l) = l := by
  cases l with
  | none => rfl
  | some l => rcases l with ⟨d,b⟩; cases d <;> simp [dualLine, dualPoint]

def projectiveDuality : ProjectivePoint F ≃ ProjectiveLine F where
  toFun := dualLine
  invFun := dualPoint
  left_inv := dualPoint_dualLine
  right_inv := dualLine_dualPoint

theorem affineDualPoint_injective : Function.Injective (affineDualPoint (F := F)) := by
  intro l m h
  have hh := congrArg dualLine h
  simpa only [affineDualPoint, dualLine_dualPoint, Option.some.injEq] using hh

theorem projective_incident_dual (P : ProjectivePoint F) (l : ProjectiveLine F) :
    ProjectiveIncident P l ↔ ProjectiveIncident (dualPoint l) (dualLine P) := by
  cases P with
  | inl p =>
    rcases p with ⟨x,y⟩
    cases l with
    | none => simp [ProjectiveIncident, dualPoint, dualLine, ThroughProjective]
    | some l =>
      rcases l with ⟨d,b⟩
      cases d with
      | none => simp [ProjectiveIncident, dualPoint, dualLine, ThroughProjective, OnLine, lineEval]
      | some m =>
        simp only [ProjectiveIncident, dualPoint, dualLine, ThroughProjective, OnLine, lineEval]
        constructor <;> intro h <;> linear_combination h
  | inr d =>
    cases d with
    | none =>
      cases l with
      | none => simp [ProjectiveIncident, dualPoint, dualLine]
      | some l =>
        rcases l with ⟨d,b⟩
        cases d <;> simp [ProjectiveIncident, dualPoint, dualLine, ThroughProjective]
    | some m =>
      cases l with
      | none => simp [ProjectiveIncident, dualPoint, dualLine, ThroughProjective]
      | some l =>
        rcases l with ⟨d,b⟩
        cases d <;> simp [ProjectiveIncident, dualPoint, dualLine, ThroughProjective, OnLine, lineEval, eq_comm]

variable [Fintype F] [DecidableEq F]

theorem missedProjective_eq_disjSum (C : Finset (Line F)) :
    missedProjective C = (missedAffine C).disjSum
      (Finset.univ \ representedDirections C) := by
  ext P
  simp only [missedProjective, Finset.mem_filter, Finset.mem_univ, true_and]
  cases P with
  | inl p => simp [missedAffine, ThroughProjective]
  | inr d =>
    simp [representedDirections, ThroughProjective]
    constructor
    · intro h b hb
      exact h d b hb rfl
    · intro h a b hab had
      subst a
      exact h b hab

theorem card_missedProjective (C : Finset (Line F)) :
    (missedProjective C).card = (missedAffine C).card +
      (Fintype.card F + 1 - (representedDirections C).card) := by
  rw [missedProjective_eq_disjSum, Finset.card_disjSum, Finset.card_sdiff]
  simp [Direction]

omit [Fintype F] in
@[simp] theorem card_dualPointSet (C : Finset (Line F)) :
    (dualPointSet C).card = C.card := by
  exact Finset.card_image_of_injective C affineDualPoint_injective

theorem mem_skew_dualLine_iff (C : Finset (Line F)) (P : ProjectivePoint F) :
    dualLine P ∈ skewProjective (dualPointSet C) ↔ P ∈ missedProjective C := by
  simp only [skewProjective, dualPointSet, missedProjective,
    Finset.mem_filter, Finset.mem_univ, true_and, Finset.forall_mem_image]
  apply forall_congr'
  intro l
  apply forall_congr'
  intro hl
  exact not_congr (projective_incident_dual P (some l)).symm

theorem card_skew_dualPointSet (C : Finset (Line F)) :
    (skewProjective (dualPointSet C)).card = (missedProjective C).card := by
  symm
  apply Finset.card_equiv projectiveDuality
  intro P
  exact (mem_skew_dualLine_iff C P).symm

theorem card_skew_dualPointSet_exact (C : Finset (Line F)) :
    (skewProjective (dualPointSet C)).card = (missedAffine C).card +
      (Fintype.card F + 1 - (representedDirections C).card) := by
  rw [card_skew_dualPointSet, card_missedProjective]

theorem card_skew_dualPointSet_le (C : Finset (Line F)) :
    (skewProjective (dualPointSet C)).card ≤
      (missedAffine C).card + Fintype.card F + 1 := by
  rw [card_skew_dualPointSet_exact]
  omega

omit [Fintype F] in
theorem card_dualPointSet_on_line (C : Finset (Line F)) (l : ProjectiveLine F) :
    ((dualPointSet C).filter (fun P => ProjectiveIncident P l)).card =
      (C.filter (fun m => ThroughProjective m (dualPoint l))).card := by
  unfold dualPointSet
  rw [Finset.filter_image, Finset.card_image_of_injective _ affineDualPoint_injective]
  congr 1
  ext m
  simp only [Finset.mem_filter]
  apply and_congr_right
  intro hm
  have hd := projective_incident_dual (dualPoint l) (some m)
  simpa only [affineDualPoint, dualLine_dualPoint, ProjectiveIncident] using hd.symm

omit [Fintype F] in
theorem dual_line_bound_gives_pencil (C : Finset (Line F)) (a : ℝ)
    (h : ∃ l : ProjectiveLine F,
      a ≤ (((dualPointSet C).filter (fun P => ProjectiveIncident P l)).card : ℝ)) :
    ∃ P : ProjectivePoint F,
      a ≤ ((C.filter (fun m => ThroughProjective m P)).card : ℝ) := by
  obtain ⟨l, hl⟩ := h
  refine ⟨dualPoint l, ?_⟩
  simpa only [card_dualPointSet_on_line] using hl

end Balanced

end OAI
