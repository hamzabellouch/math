import OAI.AlgebraicGeometry.CommutingDerivations.CoordinatePartials

namespace OAI

/-! Transport the actual coordinate partials through a specified, proved
algebra equivalence. Coefficients in the whole relative coefficient algebra
are fixed, even when the derivations are viewed over a smaller ground ring. -/
noncomputable section
namespace AbhyankarSathaye.CommutingDerivations
open MvPolynomial

variable {K B L I : Type*} [CommRing K] [CommRing B] [CommRing L]
  [Algebra K B] [Algebra K L]

def localizedPartial (e : L ≃ₐ[K] MvPolynomial I B) (i : I) : Derivation K L L :=
  transportDerivation e ((pderiv i : Derivation B (MvPolynomial I B) _).restrictScalars K)

@[simp] theorem localizedPartial_apply (e : L ≃ₐ[K] MvPolynomial I B) (i : I) (a : L) :
    localizedPartial e i a = e.symm (pderiv i (e a)) := rfl

theorem localizedPartial_locallyNilpotent (e : L ≃ₐ[K] MvPolynomial I B) (i : I) :
    LocallyNilpotent (localizedPartial e i) :=
  transportDerivation_locallyNilpotent e _ (coordinate_partial_locallyNilpotent i)

theorem localizedPartials_commute (e : L ≃ₐ[K] MvPolynomial I B) (i j : I) (a : L) :
    localizedPartial e i (localizedPartial e j a) =
      localizedPartial e j (localizedPartial e i a) := by
  simp only [localizedPartial_apply, e.apply_symm_apply, coordinate_partials_commute i j]

theorem localizedPartial_fixes_relative (e : L ≃ₐ[K] MvPolynomial I B)
    (i : I) (a : L) (b : B) (hab : e a = C b) : localizedPartial e i a = 0 := by
  rw [localizedPartial_apply, hab, pderiv_C, map_zero]

theorem localizedPartial_coordinate [DecidableEq I]
    (e : L ≃ₐ[K] MvPolynomial I B) (i j : I) :
    localizedPartial e i (e.symm (X j)) = if i = j then 1 else 0 := by
  simp [localizedPartial_apply, pderiv_X, Pi.single_apply, eq_comm]

theorem localizedPartial_kernel (e : L ≃ₐ[K] MvPolynomial I B) (i : I) (a : L) :
    localizedPartial e i a = 0 ↔ pderiv i (e a) = 0 := by
  constructor
  · intro h
    have hh := congrArg e h
    simpa only [localizedPartial_apply, e.apply_symm_apply, map_zero] using hh
  · intro h
    rw [localizedPartial_apply, h, map_zero]

theorem localizedPartials_common_kernel [IsDomain B] [CharZero B]
    (e : L ≃ₐ[K] MvPolynomial I B) (a : L) :
    (∀ i, localizedPartial e i a = 0) ↔ ∃ b : B, e a = C b := by
  simp only [localizedPartial_kernel]
  exact coordinate_partials_common_kernel (e a)

end AbhyankarSathaye.CommutingDerivations

end

end OAI
