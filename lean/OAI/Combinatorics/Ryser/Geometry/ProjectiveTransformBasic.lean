import OAI.Combinatorics.Ryser.Geometry.Basic

namespace OAI

namespace RyserCoveringCounterexample

structure ProjectiveTransform (F : Type*) [Field F] where
  points : ProjectivePoint F ≃ ProjectivePoint F
  lines : ProjectiveLine F ≃ ProjectiveLine F
  incidence : ∀ p l, ProjectiveIncidence (points p) (lines l) ↔ ProjectiveIncidence p l

namespace ProjectiveTransform

variable {F : Type*} [Field F]

def refl (F : Type*) [Field F] : ProjectiveTransform F where
  points := Equiv.refl _
  lines := Equiv.refl _
  incidence _ _ := Iff.rfl

def trans (T U : ProjectiveTransform F) : ProjectiveTransform F where
  points := T.points.trans U.points
  lines := T.lines.trans U.lines
  incidence p l := (U.incidence (T.points p) (T.lines l)).trans (T.incidence p l)

@[simp] theorem refl_points (p : ProjectivePoint F) : (refl F).points p = p := rfl

@[simp] theorem refl_lines (l : ProjectiveLine F) : (refl F).lines l = l := rfl

@[simp] theorem trans_points (T U : ProjectiveTransform F) (p : ProjectivePoint F) :
    (T.trans U).points p = U.points (T.points p) := rfl

@[simp] theorem trans_lines (T U : ProjectiveTransform F) (l : ProjectiveLine F) :
    (T.trans U).lines l = U.lines (T.lines l) := rfl

def symm (T : ProjectiveTransform F) : ProjectiveTransform F where
  points := T.points.symm
  lines := T.lines.symm
  incidence p l := by
    simpa using (T.incidence (T.points.symm p) (T.lines.symm l)).symm

end ProjectiveTransform

end RyserCoveringCounterexample

end OAI
