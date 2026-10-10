import Mathlib.Tactic
import OAI.Combinatorics.BalancedRyser.Incidence.Affine

namespace OAI

namespace Balanced
open scoped _root_.Balanced

variable {F : Type*} [Field F]

@[simp] theorem onLine_lineThrough (d : Direction F) (p : Point F) :
    OnLine p (lineThrough d p) := rfl

@[simp] theorem lineThrough_direction (d : Direction F) (p : Point F) :
    (lineThrough d p).1 = d := rfl

theorem line_eq_lineThrough (p : Point F) (l : Line F) (h : OnLine p l) :
    l = lineThrough l.1 p := by
  apply Prod.ext
  · rfl
  · exact h.symm

theorem eq_of_onLine_same_direction (p : Point F) (l m : Line F)
    (hdir : l.1 = m.1) (hl : OnLine p l) (hm : OnLine p m) : l = m := by
  rw [line_eq_lineThrough p l hl, line_eq_lineThrough p m hm, hdir]

theorem eq_of_two_common_points (p r : Point F) (hne : p ≠ r)
    (l m : Line F) (hpl : OnLine p l) (hrl : OnLine r l)
    (hpm : OnLine p m) (hrm : OnLine r m) : l = m := by
  rcases p with ⟨x, y⟩
  rcases r with ⟨x', y'⟩
  rcases l with ⟨a, c⟩
  rcases m with ⟨b, d⟩
  cases a with
  | none =>
    cases b with
    | none =>
      simp only [OnLine, lineEval] at hpl hpm
      exact Prod.ext rfl (hpl.symm.trans hpm)
    | some b =>
      simp only [OnLine, lineEval] at hpl hrl hpm hrm
      have hx : x = x' := hpl.trans hrl.symm
      have hy : y = y' := by linear_combination hpm - hrm + b * hx
      exact False.elim (hne (Prod.ext hx hy))
  | some a =>
    cases b with
    | none =>
      simp only [OnLine, lineEval] at hpl hrl hpm hrm
      have hx : x = x' := hpm.trans hrm.symm
      have hy : y = y' := by linear_combination hpl - hrl + a * hx
      exact False.elim (hne (Prod.ext hx hy))
    | some b =>
      simp only [OnLine, lineEval] at hpl hrl hpm hrm
      by_cases hab : a = b
      · subst b
        exact Prod.ext rfl (hpl.symm.trans hpm)
      · have hmul : (a - b) * (x - x') = 0 := by
          linear_combination -hpl + hrl + hpm - hrm
        have hx : x = x' := sub_eq_zero.mp
          ((mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hab))
        have hy : y = y' := by linear_combination hpl - hrl + a * hx
        exact False.elim (hne (Prod.ext hx hy))

theorem common_point_eq_of_lines_ne (l m : Line F) (hne : l ≠ m)
    (p r : Point F) (hpl : OnLine p l) (hpm : OnLine p m)
    (hrl : OnLine r l) (hrm : OnLine r m) : p = r := by
  by_contra hpr
  exact hne (eq_of_two_common_points p r hpr l m hpl hrl hpm hrm)

def linePointsEquiv : (l : Line F) → {p : Point F // OnLine p l} ≃ F
  | (none, b) =>
    { toFun := fun p => p.val.2
      invFun := fun t => ⟨(b, t), rfl⟩
      left_inv := fun p => by
        apply Subtype.ext
        apply Prod.ext
        · exact p.property.symm
        · rfl
      right_inv := fun _ => rfl }
  | (some a, b) =>
    { toFun := fun p => p.val.1
      invFun := fun t => ⟨(t, a * t + b), by
        change a * t + b - a * t = b
        ring⟩
      left_inv := fun p => by
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · have h := p.property
          change p.val.2 - a * p.val.1 = b at h
          change a * p.val.1 + b = p.val.2
          linear_combination -h
      right_inv := fun _ => rfl }

theorem onLine_lineIntersection_left (l m : Line F) (hdir : l.1 ≠ m.1) :
    OnLine (lineIntersection l m) l := by
  rcases l with ⟨a, c⟩
  rcases m with ⟨b, d⟩
  cases a with
  | none =>
    cases b with
    | none => exact False.elim (hdir rfl)
    | some b => rfl
  | some a =>
    cases b with
    | none => simp [OnLine, lineIntersection, lineEval]
    | some b => simp [OnLine, lineIntersection, lineEval]

theorem onLine_lineIntersection_right (l m : Line F) (hdir : l.1 ≠ m.1) :
    OnLine (lineIntersection l m) m := by
  rcases l with ⟨a, c⟩
  rcases m with ⟨b, d⟩
  cases a with
  | none =>
    cases b with
    | none => exact False.elim (hdir rfl)
    | some b => simp [OnLine, lineIntersection, lineEval]
  | some a =>
    cases b with
    | none => rfl
    | some b =>
      have hab : a ≠ b := fun h => hdir (congrArg some h)
      change a * ((d - c) / (a - b)) + c - b * ((d - c) / (a - b)) = d
      field_simp [sub_ne_zero.mpr hab]
      ring

def evalPairEquiv (d e : Direction F) (hne : d ≠ e) : Point F ≃ F × F where
  toFun p := (lineEval d p, lineEval e p)
  invFun x := lineIntersection (d, x.1) (e, x.2)
  left_inv p := by
    apply common_point_eq_of_lines_ne
      (d, lineEval d p) (e, lineEval e p)
      (fun h => hne (congrArg Prod.fst h))
    · exact onLine_lineIntersection_left _ _ hne
    · exact onLine_lineIntersection_right _ _ hne
    · rfl
    · rfl
  right_inv x := by
    apply Prod.ext
    · exact onLine_lineIntersection_left (d, x.1) (e, x.2) hne
    · exact onLine_lineIntersection_right (d, x.1) (e, x.2) hne

section Decidable

variable [DecidableEq F]

@[simp] theorem onLine_joiningLine_left (p r : Point F) :
    OnLine p (joiningLine p r) := by
  unfold joiningLine
  split <;> rfl

@[simp] theorem onLine_joiningLine_right (p r : Point F) :
    OnLine r (joiningLine p r) := by
  unfold joiningLine
  split
  · rename_i h
    exact h.symm
  · rename_i h
    change r.2 - (r.2 - p.2) / (r.1 - p.1) * r.1 =
      p.2 - (r.2 - p.2) / (r.1 - p.1) * p.1
    field_simp [sub_ne_zero.mpr (Ne.symm h)]
    ring

theorem existsUnique_line_of_ne (p r : Point F) (hne : p ≠ r) :
    ∃! l : Line F, OnLine p l ∧ OnLine r l := by
  refine ⟨joiningLine p r, ⟨onLine_joiningLine_left p r,
    onLine_joiningLine_right p r⟩, ?_⟩
  intro l hl
  exact eq_of_two_common_points p r hne l (joiningLine p r)
    hl.1 hl.2 (onLine_joiningLine_left p r) (onLine_joiningLine_right p r)

end Decidable

section Finite

variable [Fintype F] [DecidableEq F]

def linesThroughEquiv (p : Point F) : {l : Line F // OnLine p l} ≃ Direction F where
  toFun l := l.val.1
  invFun d := ⟨lineThrough d p, onLine_lineThrough d p⟩
  left_inv l := by
    apply Subtype.ext
    exact (line_eq_lineThrough p l.val l.property).symm
  right_inv _ := rfl

theorem card_lines_through (p : Point F) :
    ((Finset.univ : Finset (Line F)).filter fun l => OnLine p l).card =
      Fintype.card F + 1 := by
  rw [← Fintype.card_subtype]
  exact (Fintype.card_congr (linesThroughEquiv p)).trans Fintype.card_option

theorem linePoints_card (l : Line F) : (linePoints l).card = Fintype.card F := by
  unfold linePoints
  rw [← Fintype.card_subtype]
  exact Fintype.card_congr (linePointsEquiv l)

theorem linePoints_inter_card_le_one (l m : Line F) (hne : l ≠ m) :
    (linePoints l ∩ linePoints m).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro p hp r hr
  simp only [Finset.mem_inter, linePoints, Finset.mem_filter,
    Finset.mem_univ, true_and] at hp hr
  exact common_point_eq_of_lines_ne l m hne p r hp.1 hp.2 hr.1 hr.2

theorem parallel_linePoints_disjoint (l m : Line F)
    (hdir : l.1 = m.1) (hne : l ≠ m) : Disjoint (linePoints l) (linePoints m) := by
  apply Finset.disjoint_left.mpr
  intro p hp hm
  simp only [linePoints, Finset.mem_filter, Finset.mem_univ, true_and] at hp hm
  exact hne (eq_of_onLine_same_direction p l m hdir hp hm)

end Finite

end Balanced

end OAI
