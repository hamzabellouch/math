import Mathlib
import OAI.Algebra.FrobeniusObstruction.Obstruction
import OAI.Algebra.AlgebraicObstruction.EtaleCharts

namespace OAI

noncomputable section
open scoped BigOperators

namespace BoundaryOnly.FormalObstruction.FormalCorrection.AffineEtaleChart
open MvPowerSeries
variable {K α : Type} [Field K] [Finite α]

def origin : Ideal (MvPolynomial α K) := RingHom.ker MvPolynomial.constantCoeff
instance : (origin (K := K) (α := α)).IsPrime := RingHom.ker_isPrime _

instance point_liesOver (E : AffineEtaleChart K α) :
    E.point.LiesOver (origin (K := K) (α := α)) := by
  constructor
  ext p
  change MvPolynomial.constantCoeff p = 0 ↔
    constantCoeff (E.expansion (algebraMap (MvPolynomial α K) E.S p)) = 0
  rw [E.expansion.commutes]
  rfl

noncomputable instance originAlgebra (E : AffineEtaleChart K α) :
    Algebra (Localization.AtPrime (origin (K := K) (α := α))) E.LocalRing :=
  Localization.AtPrime.algebraOfLiesOver _ _

instance originLiesOverAlgebra (E : AffineEtaleChart K α) :
    IsScalarTower (MvPolynomial α K)
      (Localization.AtPrime (origin (K := K) (α := α))) E.LocalRing :=
  inferInstance

instance origin_isLocalHom (E : AffineEtaleChart K α) :
    IsLocalHom (algebraMap (Localization.AtPrime (origin (K := K) (α := α))) E.LocalRing) := by
  change IsLocalHom (Localization.localRingHom _ _ (algebraMap (MvPolynomial α K) E.S) _)
  infer_instance

omit [Finite α] in
lemma maximalIdeal_eq_map_origin (E : AffineEtaleChart K α) :
    IsLocalRing.maximalIdeal E.LocalRing =
      (origin (K := K) (α := α)).map (algebraMap (MvPolynomial α K) E.LocalRing) := by
  let R := Localization.AtPrime (origin (K := K) (α := α))
  have : Algebra.EssFiniteType R E.LocalRing :=
    Algebra.EssFiniteType.of_comp (MvPolynomial α K) R E.LocalRing
  have : Algebra.FormallyUnramified R E.LocalRing :=
    Algebra.FormallyUnramified.of_restrictScalars (MvPolynomial α K) R E.LocalRing
  rw [← Algebra.FormallyUnramified.map_maximalIdeal (R := R)]
  rw [← Localization.AtPrime.map_eq_maximalIdeal (I := origin (K := K) (α := α))]
  rw [Ideal.map_map,← IsScalarTower.algebraMap_eq (MvPolynomial α K) R E.LocalRing]

end BoundaryOnly.FormalObstruction.FormalCorrection.AffineEtaleChart

end

end OAI
