import OAI.AlgebraicGeometry.StableCoordinate.FrameScaling
import OAI.AlgebraicGeometry.StableCoordinate.CoactionLND

namespace OAI

/-!
# Coassociativity of normalized determinant-frame lifts

A polynomial algebra map with the identity specialization has the additive
group law on all four frame entries as soon as it has that law on the three
quadric products.  This is proved as an equality of two-parameter polynomial
frames, not by evaluating at field-valued parameters.
-/

noncomputable section

namespace StableCoordinate
namespace FrameLift

open Polynomial

variable {R : Type*} [CommRing R]

/-- The iterated polynomial substitution in an additive coaction. -/
def iterateHom (β : R →+* R[X]) : R →+* R[X][X] :=
  (Polynomial.mapRingHom β).comp β

/-- Substitute the sum of the two independent action parameters. -/
def addParameterHom (β : R →+* R[X]) : R →+* R[X][X] :=
  (Polynomial.taylorAlgHom (X : R[X])).toRingHom.comp
    ((Polynomial.mapRingHom (C : R →+* R[X])).comp β)

/-- Coassociativity at one particular ring element. -/
def CoassociativeAt (β : R →+* R[X]) (r : R) : Prop :=
  (β r).map β = taylor (X : R[X]) ((β r).map (C : R →+* R[X]))

@[simp]
theorem iterateHom_apply (β : R →+* R[X]) (r : R) :
    iterateHom β r = (β r).map β := rfl

@[simp]
theorem addParameterHom_apply (β : R →+* R[X]) (r : R) :
    addParameterHom β r = taylor (X : R[X]) ((β r).map (C : R →+* R[X])) := rfl

/-- The two-parameter substitutions agree at outer parameter zero. -/
theorem outer_constantCoeff_agrees (β : R →+* R[X])
    (hβ : ∀ r, (β r).coeff 0 = r) (r : R) :
    Polynomial.constantCoeff (iterateHom β r) =
      Polynomial.constantCoeff (addParameterHom β r) := by
  change ((β r).map β).coeff 0 =
    (taylor (X : R[X]) ((β r).map (C : R →+* R[X]))).coeff 0
  rw [Polynomial.coeff_map, hβ, CoactionLND.coeff_universal_translate]
  simp

/-- Group law on the base coordinates gives equality of the two iterated
frames by normalized polynomial-frame uniqueness. -/
theorem coassociative_frame [IsReduced R]
    (β : R →+* R[X]) (hβ : ∀ r, (β r).coeff 0 = r)
    (F : Frame R)
    (hbase : CoassociativeAt β (F.a*F.b) ∧
      CoassociativeAt β (F.d*F.c) ∧ CoassociativeAt β (F.d*F.b)) :
    F.map (iterateHom β) = F.map (addParameterHom β) := by
  let : IsReduced R[X] := ⟨by
    intro p hp
    ext n
    simpa using isNilpotent_iff_eq_zero.mp ((Polynomial.isNilpotent_iff.mp hp) n)⟩
  apply normalized_univariate_unique
  · change iterateHom β F.a * iterateHom β F.b =
      addParameterHom β F.a * addParameterHom β F.b ∧
      iterateHom β F.d * iterateHom β F.c =
      addParameterHom β F.d * addParameterHom β F.c ∧
      iterateHom β F.d * iterateHom β F.b =
      addParameterHom β F.d * addParameterHom β F.b
    simpa only [iterateHom_apply, addParameterHom_apply, CoassociativeAt,
      map_mul, Polynomial.map_mul, Polynomial.taylor_mul] using hbase
  · apply Frame.ext <;> exact outer_constantCoeff_agrees β hβ _

/-- Coassociativity therefore holds on each of the four frame entries. -/
theorem coassociative_on_frame_entries [IsReduced R]
    (β : R →+* R[X]) (hβ : ∀ r, (β r).coeff 0 = r)
    (F : Frame R)
    (hbase : CoassociativeAt β (F.a*F.b) ∧
      CoassociativeAt β (F.d*F.c) ∧ CoassociativeAt β (F.d*F.b)) :
    CoassociativeAt β F.a ∧ CoassociativeAt β F.d ∧
      CoassociativeAt β F.b ∧ CoassociativeAt β F.c := by
  have h := coassociative_frame β hβ F hbase
  exact ⟨congrArg Frame.a h, congrArg Frame.d h, congrArg Frame.b h, congrArg Frame.c h⟩

end FrameLift
end StableCoordinate

end

end OAI
