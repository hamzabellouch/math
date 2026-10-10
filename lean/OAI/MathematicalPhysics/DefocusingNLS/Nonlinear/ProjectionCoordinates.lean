import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.FiniteSymmetryCoordinates

namespace OAI

/-! Coordinates of a bounded projection and its exact complementary projection. -/

namespace DefocusingNLS
variable {V F : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

def projectionFrame (P : V →L[ℂ] V) (e : F ≃L[ℂ] P.range) : F →L[ℂ] V :=
  P.range.subtypeL.comp e.toContinuousLinearMap

def projectionCoordinates (P : V →L[ℂ] V) (e : F ≃L[ℂ] P.range) : V →L[ℂ] F :=
  e.symm.toContinuousLinearMap.comp P.rangeRestrict

theorem idempotent_range_fixed (P : V →L[ℂ] V) (hP : IsIdempotentElem P) (v : P.range) :
    P (v : V)=(v : V) := by
  obtain ⟨w,hw⟩ := v.property
  rw [← hw]
  exact congrArg (fun L : V →L[ℂ] V => L w) hP

theorem projectionCoordinates_frame (P : V →L[ℂ] V) (hP : IsIdempotentElem P)
    (e : F ≃L[ℂ] P.range) (v : F) :
    projectionCoordinates P e (projectionFrame P e v)=v := by
  have hfix : P.rangeRestrict (e v : V)=e v :=
    Subtype.ext (idempotent_range_fixed P hP (e v))
  change e.symm (P.rangeRestrict (e v : V))=v
  rw [hfix,e.symm_apply_apply]

theorem projectionFrame_coordinates (P : V →L[ℂ] V)
    (e : F ≃L[ℂ] P.range) (v : V) :
    projectionFrame P e (projectionCoordinates P e v)=P v := by
  change (e (e.symm (P.rangeRestrict v)) : V)=P v
  rw [e.apply_symm_apply]
  rfl

theorem projectionCoordinates_zero_iff (P : V →L[ℂ] V)
    (e : F ≃L[ℂ] P.range) (v : V) : projectionCoordinates P e v=0 ↔ P v=0 := by
  constructor
  · intro h
    rw [← projectionFrame_coordinates P e v,h,map_zero]
  · intro h
    have hz : P.rangeRestrict v=0 := Subtype.ext h
    change e.symm (P.rangeRestrict v)=0
    rw [hz,map_zero]

end DefocusingNLS

end OAI
