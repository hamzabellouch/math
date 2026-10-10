import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import OAI.NumberTheory.SiegelZeros.Intersection.TorusPolynomial

namespace OAI

namespace SiegelZeros

section

noncomputable section
namespace W58

variable (K : Type*) [Field K]

theorem torus_integrallyClosed : IsIntegrallyClosed (TorusRing K) := by
  exact isIntegrallyClosed_of_isLocalization (TorusRing K)
    (Submonoid.powers (coordinateProduct K))
    (powers_le_nonZeroDivisors_of_noZeroDivisors (W17.coordinateProduct_ne_zero K))

theorem generic_local_isDomain (p : Ideal (TorusRing K)) [p.IsPrime] :
    IsDomain (GenericLocalRing K p) := by
  let := W17.torus_isDomain K
  exact IsLocalization.isDomain_of_le_nonZeroDivisors (GenericLocalRing K p)
    p.primeCompl_le_nonZeroDivisors

attribute [local instance] generic_local_isDomain

theorem generic_local_integrallyClosed (p : Ideal (TorusRing K)) [p.IsPrime] :
    IsIntegrallyClosed (GenericLocalRing K p) := by
  let := W17.torus_isDomain K
  let := torus_integrallyClosed K
  exact isIntegrallyClosed_of_isLocalization (GenericLocalRing K p)
    p.primeCompl p.primeCompl_le_nonZeroDivisors

theorem dvr_of_local_normal_dimension_one (R : Type*) [CommRing R] [IsDomain R]
    [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (hdim : ringKrullDim R = 1) : IsDiscreteValuationRing R := by
  have hnotfield : ¬ IsField R := by
    intro h
    have hz := ringKrullDim_eq_zero_of_isField h
    rw [hdim] at hz
    exact one_ne_zero hz
  have hkrull : Ring.KrullDimLE 1 R := (Ring.krullDimLE_iff).2 (le_of_eq hdim)
  let : Ring.DimensionLEOne R :=
    ⟨fun {p} hp hprime => (Ring.krullDimLE_one_iff_of_noZeroDivisors.mp hkrull) p hp hprime⟩
  have hdedekind : IsDedekindDomain R := by
    refine (isDedekindDomain_iff R (FractionRing R)).2
      ⟨inferInstance, inferInstance, inferInstance, ?_⟩
    exact (isIntegrallyClosed_iff (FractionRing R)).mp inferInstance
  exact ((IsDiscreteValuationRing.TFAE R hnotfield).out 1 3).mpr hdedekind

theorem generic_local_dvr_of_height_one (p : Ideal (TorusRing K)) [p.IsPrime]
    (hp : p.height = 1) : IsDiscreteValuationRing (GenericLocalRing K p) := by
  let := generic_local_isDomain K p
  let := generic_local_integrallyClosed K p
  apply dvr_of_local_normal_dimension_one
  simpa [hp] using generic_local_dimension K p

theorem generic_cotangent_finrank_of_height_one (p : Ideal (TorusRing K)) [p.IsPrime]
    (hp : p.height = 1) :
    Module.finrank (IsLocalRing.ResidueField (GenericLocalRing K p))
      (GenericCotangent K p) = 1 := by
  let := generic_local_isDomain K p
  exact (IsLocalRing.finrank_CotangentSpace_eq_one_iff
    (R := GenericLocalRing K p)).mpr
    (generic_local_dvr_of_height_one K p hp)

theorem generic_local_regular_of_height_one (p : Ideal (TorusRing K)) [p.IsPrime]
    (hp : p.height = 1) : IsRegularLocalRing (GenericLocalRing K p) := by
  apply (generic_regular_iff_cotangent_dimension K p).mpr
  simpa [hp] using congrArg (fun n : ℕ => (n : WithBot ℕ∞))
    (generic_cotangent_finrank_of_height_one K p hp)

end W58

end

end

end SiegelZeros

end OAI
