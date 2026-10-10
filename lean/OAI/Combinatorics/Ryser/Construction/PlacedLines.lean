import OAI.Combinatorics.Ryser.Construction.DirectionPlacement

namespace OAI

namespace RyserCoveringCounterexample.Construction

variable {k : Type*} [Field k]

def lineAnchor (l : AffineLine k) : Point k :=
  match l.1 with
  | none => (l.2, 0)
  | some _ => (0, l.2)

@[simp] theorem projection_lineAnchor (l : AffineLine k) :
    projection l.1 (lineAnchor l) = l.2 := by
  obtain ⟨d, c⟩ := l
  cases d <;> simp [lineAnchor, projection]

@[simp] theorem incidence_lineAnchor (l : AffineLine k) :
    Incidence (lineAnchor l) l :=
  projection_lineAnchor l

variable {F : Type*} [Field F] [DecidableEq F] [instDecidableEqk : DecidableEq k]

def placedLine (σ : k →+* F) (M : PlaneLinearMap F) (b : Point F)
    (l : AffineLine k) : AffineLine F :=
  lineThrough (placedDirection σ M l.1) (placedPoint σ M b (lineAnchor l))

@[simp] theorem placedLine_direction (σ : k →+* F) (M : PlaneLinearMap F)
    (b : Point F) (l : AffineLine k) :
    (placedLine σ M b l).1 = placedDirection σ M l.1 := let _ := instDecidableEqk; rfl

theorem incidence_placedLine_iff (σ : k →+* F) (M : PlaneLinearMap F)
    (b : Point F) (p : Point k) (l : AffineLine k) :
    Incidence (placedPoint σ M b p) (placedLine σ M b l) ↔ Incidence p l := by
  change projection (placedDirection σ M l.1) (placedPoint σ M b p) =
      projection (placedDirection σ M l.1) (placedPoint σ M b (lineAnchor l)) ↔
    projection l.1 p = l.2
  rw [projection_placedPoint_eq_iff, projection_lineAnchor]

theorem placedLine_injective (σ : k →+* F) (M : PlaneLinearMap F)
    (b : Point F) : Function.Injective (placedLine σ M b) := by
  intro l m hlm
  have hdir : l.1 = m.1 :=
    placedDirection_injective σ M (congrArg Prod.fst hlm)
  have hinc : Incidence (lineAnchor l) m := by
    apply (incidence_placedLine_iff σ M b (lineAnchor l) m).mp
    rw [← hlm]
    exact (incidence_placedLine_iff σ M b (lineAnchor l) l).mpr
      (incidence_lineAnchor l)
  exact line_eq_of_direction_eq_of_incidence hdir (incidence_lineAnchor l) hinc

theorem eq_placedLine_of_direction_of_incidence
    (σ : k →+* F) (M : PlaneLinearMap F) (b : Point F)
    (p : Point k) (d : Direction k) (ell : AffineLine F)
    (hdir : ell.1 = placedDirection σ M d)
    (hinc : Incidence (placedPoint σ M b p) ell) :
    ell = placedLine σ M b (d, projection d p) := by
  apply line_eq_of_direction_eq_of_incidence
  · exact hdir
  · exact hinc
  · exact (incidence_placedLine_iff σ M b p (d, projection d p)).mpr rfl

end RyserCoveringCounterexample.Construction

end OAI
