import OAI.Combinatorics.Ryser.Construction.PlacedLines

namespace OAI

namespace RyserCoveringCounterexample.Construction

variable {k F : Type*} [Field k] [Field F] [DecidableEq k] [DecidableEq F]

theorem mem_range_placedPoint_of_incident_of_ne_placedLines
    (σ : k →+* F) (M : PlaneLinearMap F) (b : Point F)
    {p : Point F} {l m : AffineLine k}
    (hlm : placedLine σ M b l ≠ placedLine σ M b m)
    (hpl : Incidence p (placedLine σ M b l))
    (hpm : Incidence p (placedLine σ M b m)) :
    p ∈ Set.range (placedPoint σ M b) := by
  have hdir : l.1 ≠ m.1 := by
    intro hsame
    have hplaced : (placedLine σ M b l).1 = (placedLine σ M b m).1 := by
      simpa only [placedLine_direction] using congrArg (placedDirection σ M) hsame
    exact hlm (line_eq_of_direction_eq_of_incidence
      (l := placedLine σ M b l) (m := placedLine σ M b m) (p := p)
      hplaced hpl hpm)
  obtain ⟨q, hq, _⟩ := existsUnique_incident_of_ne_direction l m hdir
  have hql : Incidence (placedPoint σ M b q) (placedLine σ M b l) :=
    (incidence_placedLine_iff σ M b q l).2 hq.1
  have hqm : Incidence (placedPoint σ M b q) (placedLine σ M b m) :=
    (incidence_placedLine_iff σ M b q m).2 hq.2
  have hpq : p = placedPoint σ M b q :=
    eq_of_common_incidence_of_ne_lines hlm hpl hpm hql hqm
  exact ⟨q, hpq.symm⟩

theorem eq_placedLine_of_incident_of_notMem_range
    (σ : k →+* F) (M : PlaneLinearMap F) (b : Point F)
    {p : Point F} {l m : AffineLine k}
    (houtside : p ∉ Set.range (placedPoint σ M b))
    (hpl : Incidence p (placedLine σ M b l))
    (hpm : Incidence p (placedLine σ M b m)) :
    placedLine σ M b l = placedLine σ M b m := by
  by_contra hlm
  exact houtside (mem_range_placedPoint_of_incident_of_ne_placedLines σ M b hlm hpl hpm)

theorem eq_smallLine_of_incident_of_notMem_range
    (σ : k →+* F) (M : PlaneLinearMap F) (b : Point F)
    {p : Point F} {l m : AffineLine k}
    (houtside : p ∉ Set.range (placedPoint σ M b))
    (hpl : Incidence p (placedLine σ M b l))
    (hpm : Incidence p (placedLine σ M b m)) : l = m :=
  placedLine_injective σ M b
    (eq_placedLine_of_incident_of_notMem_range σ M b houtside hpl hpm)

end RyserCoveringCounterexample.Construction

end OAI
