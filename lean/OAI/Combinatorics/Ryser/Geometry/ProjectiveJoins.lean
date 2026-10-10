import OAI.Combinatorics.Ryser.Geometry.AffineJoins

namespace OAI

namespace RyserCoveringCounterexample

variable {F : Type*} [Field F]

theorem existsUnique_projectiveLine_of_ne {p q : ProjectivePoint F}
    (hpq : p ≠ q) :
    ∃! l : ProjectiveLine F, ProjectiveIncidence p l ∧ ProjectiveIncidence q l := by
  classical
  cases p with
  | inl p =>
    cases q with
    | inl q =>
      have hpq' : p ≠ q := fun h => hpq (congrArg Sum.inl h)
      obtain ⟨l, hl, huniq⟩ := existsUnique_lineThrough_pair hpq'
      refine ⟨some l, hl, ?_⟩
      intro m hm
      cases m with
      | none => exact hm.1.elim
      | some m => exact congrArg some (huniq m hm)
    | inr d =>
      refine ⟨some (lineThrough d p), ⟨rfl, rfl⟩, ?_⟩
      intro m hm
      cases m with
      | none => exact hm.1.elim
      | some m =>
        apply congrArg some
        exact line_eq_of_direction_eq_of_incidence hm.2.symm hm.1 rfl
  | inr d =>
    cases q with
    | inl q =>
      refine ⟨some (lineThrough d q), ⟨rfl, rfl⟩, ?_⟩
      intro m hm
      cases m with
      | none => exact hm.2.elim
      | some m =>
        apply congrArg some
        exact line_eq_of_direction_eq_of_incidence hm.1.symm hm.2 rfl
    | inr e =>
      refine ⟨none, ⟨trivial, trivial⟩, ?_⟩
      intro m hm
      cases m with
      | none => rfl
      | some m =>
        have hde : d = e := hm.1.trans hm.2.symm
        exact (hpq (congrArg Sum.inr hde)).elim

theorem existsUnique_projectivePoint_of_ne {l m : ProjectiveLine F}
    (hlm : l ≠ m) :
    ∃! p : ProjectivePoint F, ProjectiveIncidence p l ∧ ProjectiveIncidence p m := by
  classical
  cases l with
  | none =>
    cases m with
    | none => exact (hlm rfl).elim
    | some m =>
      refine ⟨Sum.inr m.1, ⟨trivial, rfl⟩, ?_⟩
      intro p hp
      cases p with
      | inl p => exact hp.1.elim
      | inr d => exact congrArg Sum.inr hp.2
  | some l =>
    cases m with
    | none =>
      refine ⟨Sum.inr l.1, ⟨rfl, trivial⟩, ?_⟩
      intro p hp
      cases p with
      | inl p => exact hp.2.elim
      | inr d => exact congrArg Sum.inr hp.1
    | some m =>
      by_cases hdir : l.1 = m.1
      · refine ⟨Sum.inr l.1, ⟨rfl, hdir⟩, ?_⟩
        intro p hp
        cases p with
        | inl p =>
          have heq : l = m := line_eq_of_direction_eq_of_incidence hdir hp.1 hp.2
          exact (hlm (congrArg some heq)).elim
        | inr d => exact congrArg Sum.inr hp.1
      · obtain ⟨p, hp, huniq⟩ := existsUnique_incident_of_ne_direction l m hdir
        refine ⟨Sum.inl p, hp, ?_⟩
        intro q hq
        cases q with
        | inl q => exact congrArg Sum.inl (huniq q hq)
        | inr d => exact (hdir (hq.1.symm.trans hq.2)).elim

theorem eq_projectiveLine_of_common_incidence
    {p q : ProjectivePoint F} {l m : ProjectiveLine F}
    (hpq : p ≠ q)
    (hpl : ProjectiveIncidence p l) (hql : ProjectiveIncidence q l)
    (hpm : ProjectiveIncidence p m) (hqm : ProjectiveIncidence q m) : l = m := by
  obtain ⟨k, _, huniq⟩ := existsUnique_projectiveLine_of_ne hpq
  exact (huniq l ⟨hpl, hql⟩).trans (huniq m ⟨hpm, hqm⟩).symm

theorem eq_projectivePoint_of_common_incidence
    {l m : ProjectiveLine F} {p q : ProjectivePoint F}
    (hlm : l ≠ m)
    (hpl : ProjectiveIncidence p l) (hpm : ProjectiveIncidence p m)
    (hql : ProjectiveIncidence q l) (hqm : ProjectiveIncidence q m) : p = q := by
  obtain ⟨x, _, huniq⟩ := existsUnique_projectivePoint_of_ne hlm
  exact (huniq p ⟨hpl, hpm⟩).trans (huniq q ⟨hql, hqm⟩).symm

theorem existsUnique_projective_incident_of_ne_lines {l m : AffineLine F}
    (hlm : l ≠ m) :
    ∃! p : ProjectivePoint F,
      ProjectiveIncidence p (some l) ∧ ProjectiveIncidence p (some m) := by
  apply existsUnique_projectivePoint_of_ne
  intro h
  exact hlm (Option.some.inj h)

theorem existsUnique_projectivePoint_of_ne_affineLines {l m : AffineLine F}
    (hlm : l ≠ m) :
    ∃! p : ProjectivePoint F,
      ProjectiveIncidence p (some l) ∧ ProjectiveIncidence p (some m) :=
  existsUnique_projective_incident_of_ne_lines hlm

theorem eq_affineLine_of_common_projective_incidence
    {p q : ProjectivePoint F} {l m : AffineLine F}
    (hpq : p ≠ q)
    (hpl : ProjectiveIncidence p (some l))
    (hql : ProjectiveIncidence q (some l))
    (hpm : ProjectiveIncidence p (some m))
    (hqm : ProjectiveIncidence q (some m)) : l = m :=
  Option.some.inj (eq_projectiveLine_of_common_incidence hpq hpl hql hpm hqm)

theorem not_projectiveIncidence_infty_of_ne_direction
    {d e : Direction F} (hde : d ≠ e) {l : AffineLine F} :
    ¬ (ProjectiveIncidence (Sum.inr d) (some l) ∧
      ProjectiveIncidence (Sum.inr e) (some l)) := by
  intro h
  exact hde (h.1.trans h.2.symm)

theorem ne_of_projectiveIncidence_of_not_projectiveIncidence
    {p q : ProjectivePoint F} {l : ProjectiveLine F}
    (hpl : ProjectiveIncidence p l) (hql : ¬ ProjectiveIncidence q l) : p ≠ q := by
  intro hpq
  exact hql (hpq ▸ hpl)

end RyserCoveringCounterexample

end OAI
