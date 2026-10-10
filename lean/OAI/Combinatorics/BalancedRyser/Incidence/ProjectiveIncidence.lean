import OAI.Combinatorics.BalancedRyser.Incidence.AffineIncidence
import OAI.Combinatorics.BalancedRyser.Incidence.Projective2

namespace OAI

namespace Balanced
open scoped _root_.Balanced

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def projectiveLinePoints (l : ProjectiveLine F) : Finset (ProjectivePoint F) :=
  Finset.univ.filter (fun P => ProjectiveIncident P l)

def projectivePencil (P : ProjectivePoint F) : Finset (ProjectiveLine F) :=
  Finset.univ.filter (ProjectiveIncident P)

@[simp] theorem mem_projectiveLinePoints (l : ProjectiveLine F) (P : ProjectivePoint F) :
    P ∈ projectiveLinePoints l ↔ ProjectiveIncident P l := by
  simp [projectiveLinePoints]

@[simp] theorem mem_projectivePencil (P : ProjectivePoint F) (l : ProjectiveLine F) :
    l ∈ projectivePencil P ↔ ProjectiveIncident P l := by
  simp [projectivePencil]

theorem projectiveLinePoints_some (l : Line F) :
    projectiveLinePoints (some l) = (linePoints l).disjSum {l.1} := by
  ext P
  rw [mem_projectiveLinePoints]
  cases P <;> simp [linePoints, ProjectiveIncident,
    ThroughProjective, eq_comm]

theorem projectiveLinePoints_none :
    projectiveLinePoints (none : ProjectiveLine F) =
      (∅ : Finset (Point F)).disjSum Finset.univ := by
  ext P
  rw [mem_projectiveLinePoints]
  cases P <;> simp [ProjectiveIncident]

theorem card_projectiveLinePoints (l : ProjectiveLine F) :
    (projectiveLinePoints l).card = Fintype.card F + 1 := by
  cases l with
  | none => simp [projectiveLinePoints_none, Direction]
  | some l => simp [projectiveLinePoints_some, linePoints_card]

theorem card_projectivePencil (P : ProjectivePoint F) :
    (projectivePencil P).card = Fintype.card F + 1 := by
  have h : (projectiveLinePoints (dualLine P)).card = (projectivePencil P).card := by
    apply Finset.card_equiv projectiveDuality
    intro Q
    simp only [mem_projectiveLinePoints, mem_projectivePencil]
    change ProjectiveIncident Q (dualLine P) ↔ ProjectiveIncident P (dualLine Q)
    simpa only [dualPoint_dualLine] using (projective_incident_dual P (dualLine Q)).symm
  rw [← h, card_projectiveLinePoints]

def projectiveJoin : ProjectivePoint F → ProjectivePoint F → ProjectiveLine F
  | Sum.inl p, Sum.inl r => some (joiningLine p r)
  | Sum.inl p, Sum.inr d => some (lineThrough d p)
  | Sum.inr d, Sum.inl p => some (lineThrough d p)
  | Sum.inr _, Sum.inr _ => none

omit [Fintype F] in
@[simp] theorem projectiveIncident_join_left (P Q : ProjectivePoint F) :
    ProjectiveIncident P (projectiveJoin P Q) := by
  cases P <;> cases Q <;>
    simp [projectiveJoin, ProjectiveIncident, ThroughProjective]

omit [Fintype F] in
@[simp] theorem projectiveIncident_join_right (P Q : ProjectivePoint F) :
    ProjectiveIncident Q (projectiveJoin P Q) := by
  cases P <;> cases Q <;>
    simp [projectiveJoin, ProjectiveIncident, ThroughProjective]

omit [Fintype F] in

theorem eq_projectiveJoin_of_incident (P Q : ProjectivePoint F) (hPQ : P ≠ Q)
    (l : ProjectiveLine F) (hP : ProjectiveIncident P l)
    (hQ : ProjectiveIncident Q l) : l = projectiveJoin P Q := by
  cases P with
  | inl p =>
    cases Q with
    | inl q =>
      cases l with
      | none => exact False.elim hP
      | some l =>
        apply congrArg some
        exact eq_of_two_common_points p q (fun h => hPQ (congrArg Sum.inl h))
          l (joiningLine p q) hP hQ (onLine_joiningLine_left p q)
          (onLine_joiningLine_right p q)
    | inr d =>
      cases l with
      | none => exact False.elim hP
      | some l =>
        apply congrArg some
        change l.1 = d at hQ
        rw [line_eq_lineThrough p l hP, hQ]
  | inr d =>
    cases Q with
    | inl p =>
      cases l with
      | none => exact False.elim hQ
      | some l =>
        apply congrArg some
        change l.1 = d at hP
        rw [line_eq_lineThrough p l hQ, hP]
    | inr e =>
      cases l with
      | none => rfl
      | some l =>
        change l.1 = d at hP
        change l.1 = e at hQ
        exact False.elim (hPQ (congrArg Sum.inr (hP.symm.trans hQ)))

omit [Fintype F] in
theorem eq_of_two_common_projective_points (P Q : ProjectivePoint F) (hPQ : P ≠ Q)
    (l m : ProjectiveLine F) (hPl : ProjectiveIncident P l)
    (hQl : ProjectiveIncident Q l) (hPm : ProjectiveIncident P m)
    (hQm : ProjectiveIncident Q m) : l = m :=
  (eq_projectiveJoin_of_incident P Q hPQ l hPl hQl).trans
    (eq_projectiveJoin_of_incident P Q hPQ m hPm hQm).symm

end Balanced

end OAI
