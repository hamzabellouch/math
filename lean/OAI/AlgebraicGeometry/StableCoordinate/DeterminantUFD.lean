import OAI.AlgebraicGeometry.StableCoordinate.DeterminantPrimeA
import OAI.AlgebraicGeometry.StableCoordinate.DeterminantCharts
import Mathlib.RingTheory.Ideal.UFD

namespace OAI

/-!
# Unique factorization in the determinant ring

The prime element `a` has a localization which is a polynomial algebra over a
localization of a polynomial algebra.  Nagata's prime-element criterion then
proves unique factorization in the actual determinant quotient.
-/

namespace StableCoordinate.DeterminantRing

variable (k : Type*) [CommRing k] [IsNoetherianRing k]

variable [IsDomain k] [UniqueFactorizationMonoid k]

instance C_isNoetherianRing : IsNoetherianRing (C k) := inferInstance

noncomputable instance C_uniqueFactorizationMonoid : UniqueFactorizationMonoid (C k) := by
  apply (UniqueFactorizationMonoid.iff_localizationAway_of_prime (a_prime k)).mpr
  exact (chartEquivA k).symm.toMulEquiv.uniqueFactorizationMonoid inferInstance

end StableCoordinate.DeterminantRing

namespace StableCoordinate.Obstruction

variable (k : Type*) [CommRing k] [IsNoetherianRing k]

instance C_isNoetherianRing : IsNoetherianRing (C k) := inferInstance

variable [IsDomain k] [UniqueFactorizationMonoid k]

/-- The canonical obstruction presentation is definitionally the determinant ring. -/
noncomputable instance C_uniqueFactorizationMonoid : UniqueFactorizationMonoid (C k) :=
  DeterminantRing.C_uniqueFactorizationMonoid k

end StableCoordinate.Obstruction

end OAI
