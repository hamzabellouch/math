import OAI.Combinatorics.Ryser.Geometry.Basic
import Mathlib.Tactic.Ring

namespace OAI

namespace RyserCoveringCounterexample

variable {F : Type*} [Field F]

theorem point_eq_of_projection_eq_of_ne_direction
    {d e : Direction F} {p q : Point F} (hde : d ≠ e)
    (hd : projection d p = projection d q)
    (he : projection e p = projection e q) : p = q := by
  rcases p with ⟨x, y⟩
  rcases q with ⟨z, w⟩
  cases d with
  | none =>
    cases e with
    | none => exact (hde rfl).elim
    | some b =>
      change x = z at hd
      change y - b * x = w - b * z at he
      apply Prod.ext hd
      calc
        y = (y - b * x) + b * x := by ring
        _ = (w - b * z) + b * z := by rw [he, hd]
        _ = w := by ring
  | some a =>
    cases e with
    | none =>
      change y - a * x = w - a * z at hd
      change x = z at he
      apply Prod.ext he
      calc
        y = (y - a * x) + a * x := by ring
        _ = (w - a * z) + a * z := by rw [hd, he]
        _ = w := by ring
    | some b =>
      have hab : a ≠ b := fun h => hde (congrArg Option.some h)
      change y - a * x = w - a * z at hd
      change y - b * x = w - b * z at he
      have hmul : (a - b) * x = (a - b) * z := by
        calc
          (a - b) * x = (y - b * x) - (y - a * x) := by ring
          _ = (w - b * z) - (w - a * z) := by rw [he, hd]
          _ = (a - b) * z := by ring
      have hx : x = z := mul_left_cancel₀ (sub_ne_zero.mpr hab) hmul
      apply Prod.ext hx
      calc
        y = (y - a * x) + a * x := by ring
        _ = (w - a * z) + a * z := by rw [hd, hx]
        _ = w := by ring

theorem line_eq_of_direction_eq_of_incidence
    {l m : AffineLine F} {p : Point F} (hdl : l.1 = m.1)
    (hpl : Incidence p l) (hpm : Incidence p m) : l = m := by
  change projection l.1 p = l.2 at hpl
  change projection m.1 p = m.2 at hpm
  apply Prod.ext hdl
  exact hpl.symm.trans ((congrArg (fun d => projection d p) hdl).trans hpm)

theorem not_incidence_of_same_direction_of_ne
    {l m : AffineLine F} {p : Point F} (hdl : l.1 = m.1)
    (hlm : l ≠ m) (hpl : Incidence p l) : ¬Incidence p m :=
  fun hpm => hlm (line_eq_of_direction_eq_of_incidence hdl hpl hpm)

theorem line_eq_of_two_incident_points
    {p q : Point F} {l m : AffineLine F} (hpq : p ≠ q)
    (hpl : Incidence p l) (hql : Incidence q l)
    (hpm : Incidence p m) (hqm : Incidence q m) : l = m := by
  by_cases hdir : l.1 = m.1
  · exact line_eq_of_direction_eq_of_incidence hdir hpl hpm
  · change projection l.1 p = l.2 at hpl
    change projection l.1 q = l.2 at hql
    change projection m.1 p = m.2 at hpm
    change projection m.1 q = m.2 at hqm
    exact (hpq (point_eq_of_projection_eq_of_ne_direction hdir
      (hpl.trans hql.symm) (hpm.trans hqm.symm))).elim

theorem eq_of_common_incidence_of_ne_lines
    {l m : AffineLine F} {p q : Point F} (hlm : l ≠ m)
    (hpl : Incidence p l) (hpm : Incidence p m)
    (hql : Incidence q l) (hqm : Incidence q m) : p = q := by
  by_contra hpq
  exact hlm (line_eq_of_two_incident_points hpq hpl hql hpm hqm)

theorem existsUnique_incident_of_ne_direction (l m : AffineLine F)
    (hdir : l.1 ≠ m.1) :
    ∃! p : Point F, Incidence p l ∧ Incidence p m := by
  have hex : ∃ p : Point F, Incidence p l ∧ Incidence p m := by
    rcases l with ⟨d, b⟩
    rcases m with ⟨e, c⟩
    change d ≠ e at hdir
    cases d with
    | none =>
      cases e with
      | none => exact (hdir rfl).elim
      | some a =>
        refine ⟨(b, c + a * b), ?_⟩
        change b = b ∧ (c + a * b) - a * b = c
        exact ⟨rfl, by ring⟩
    | some a =>
      cases e with
      | none =>
        refine ⟨(c, b + a * c), ?_⟩
        change (b + a * c) - a * c = b ∧ c = c
        exact ⟨by ring, rfl⟩
      | some a' =>
        have haa : a ≠ a' := fun h => hdir (congrArg Option.some h)
        have hne : a - a' ≠ 0 := sub_ne_zero.mpr haa
        let x : F := (c - b) / (a - a')
        have hx : x * (a - a') = c - b := by
          change (c - b) / (a - a') * (a - a') = c - b
          exact div_mul_cancel₀ (c - b) hne
        refine ⟨(x, b + a * x), ?_⟩
        change (b + a * x) - a * x = b ∧ (b + a * x) - a' * x = c
        constructor
        · ring
        · calc
            (b + a * x) - a' * x = b + x * (a - a') := by ring
            _ = b + (c - b) := by rw [hx]
            _ = c := by ring
  obtain ⟨p, hp⟩ := hex
  refine ⟨p, hp, ?_⟩
  intro q hq
  change projection l.1 p = l.2 ∧ projection m.1 p = m.2 at hp
  change projection l.1 q = l.2 ∧ projection m.1 q = m.2 at hq
  exact point_eq_of_projection_eq_of_ne_direction hdir
    (hq.1.trans hp.1.symm) (hq.2.trans hp.2.symm)

section Join

variable [DecidableEq F]

def joinDirection (p q : Point F) : Direction F :=
  if p.1 = q.1 then none else some ((q.2 - p.2) / (q.1 - p.1))

def joinLine (p q : Point F) : AffineLine F :=
  lineThrough (joinDirection p q) p

@[simp] theorem incidence_joinLine_left (p q : Point F) :
    Incidence p (joinLine p q) := rfl

@[simp] theorem incidence_joinLine_right (p q : Point F) :
    Incidence q (joinLine p q) := by
  change projection (joinDirection p q) q = projection (joinDirection p q) p
  by_cases hx : p.1 = q.1
  · have hd : joinDirection p q = none := by
      unfold joinDirection
      exact ite_eq_left hx
    simpa only [hd, projection] using hx.symm
  · let a : F := (q.2 - p.2) / (q.1 - p.1)
    have hd : joinDirection p q = some a := by
      unfold joinDirection
      exact ite_eq_right hx
    have hden : q.1 - p.1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
    have hs : a * (q.1 - p.1) = q.2 - p.2 := by
      change (q.2 - p.2) / (q.1 - p.1) * (q.1 - p.1) = q.2 - p.2
      exact div_mul_cancel₀ (q.2 - p.2) hden
    simp only [hd, projection]
    calc
      q.2 - a * q.1 = p.2 - a * p.1 +
          ((q.2 - p.2) - a * (q.1 - p.1)) := by ring
      _ = p.2 - a * p.1 := by rw [hs]; ring

theorem lineThrough_joinDirection_eq (p q : Point F) :
    lineThrough (joinDirection p q) q = joinLine p q := by
  apply line_eq_of_direction_eq_of_incidence
    (l := lineThrough (joinDirection p q) q) (m := joinLine p q) (p := q) rfl
  · rfl
  · exact incidence_joinLine_right p q

theorem eq_joinLine_of_incidence {p q : Point F} {l : AffineLine F}
    (hpq : p ≠ q) (hpl : Incidence p l) (hql : Incidence q l) :
    l = joinLine p q :=
  line_eq_of_two_incident_points hpq hpl hql
    (incidence_joinLine_left p q) (incidence_joinLine_right p q)

theorem existsUnique_lineThrough_pair {p q : Point F} (hpq : p ≠ q) :
    ∃! l : AffineLine F, Incidence p l ∧ Incidence q l := by
  refine ⟨joinLine p q, ⟨incidence_joinLine_left p q,
    incidence_joinLine_right p q⟩, ?_⟩
  intro l hl
  exact eq_joinLine_of_incidence hpq hl.1 hl.2

theorem projection_eq_iff_eq_joinDirection {p q : Point F} (hpq : p ≠ q)
    (d : Direction F) :
    projection d p = projection d q ↔ d = joinDirection p q := by
  constructor
  · intro hd
    have hpl : Incidence p (lineThrough d p) := rfl
    have hql : Incidence q (lineThrough d p) := by
      change projection d q = projection d p
      exact hd.symm
    have hl := eq_joinLine_of_incidence hpq hpl hql
    have hf := congrArg Prod.fst hl
    change d = joinDirection p q at hf
    exact hf
  · intro hd
    subst d
    have hq := incidence_joinLine_right p q
    change projection (joinDirection p q) q = projection (joinDirection p q) p at hq
    exact hq.symm

theorem existsUnique_direction_of_ne {p q : Point F} (hpq : p ≠ q) :
    ∃! d : Direction F, projection d p = projection d q := by
  refine ⟨joinDirection p q,
    (projection_eq_iff_eq_joinDirection hpq _).mpr rfl, ?_⟩
  intro d hd
  exact (projection_eq_iff_eq_joinDirection hpq d).mp hd

end Join

end RyserCoveringCounterexample

end OAI
