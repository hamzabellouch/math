import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Length
import OAI.NumberTheory.SiegelZeros.Differentials.DerivativeGeneratorBridge

namespace OAI

namespace SiegelZeros

noncomputable section
namespace SiegelZerosAwei.W21

open SiegelZeros.W58
variable {K : Type*} [Field K]

local instance (P : Ideal (TorusRing K)) [P.IsPrime] :
    HasQuotient (Localization.AtPrime P) (Ideal (Localization.AtPrime P)) :=
  @Ideal.instHasQuotient (Localization.AtPrime P) inferInstance

theorem prime_eq_identityIdeal_of_height_four
    (P : Ideal (TorusRing K)) [P.IsPrime]
    (hPid : P ≤ identityIdeal K) (hp : P.height = 4) :
    P = identityIdeal K := by
  have hM : (identityIdeal K).height ≤ 4 := by
    have hh := (ringKrullDim_le_iff_height_le 4).mp
      (torus_dimension_le_four K) (show (identityIdeal K).IsPrime from inferInstance)
    exact WithBot.coe_le_coe.mp hh
  by_contra hne
  have hstep := prime_height_toNat_succ_le (le_of_eq hp) hM
    (lt_of_le_of_ne hPid hne)
  have hbound : (identityIdeal K).height.toNat ≤ 4 :=
    ENat.toNat_le_of_le_natCast (n := 4) hM
  rw [hp] at hstep
  change 4 + 1 ≤ (identityIdeal K).height.toNat at hstep
  omega

def heightFourLocalRingEquiv (P : Ideal (TorusRing K)) [P.IsPrime]
    (hPid : P ≤ identityIdeal K) (hp : P.height = 4) :
    Localization.AtPrime P ≃+* Localization.AtPrime (identityIdeal K) := by
  have heq := prime_eq_identityIdeal_of_height_four P hPid hp
  subst P
  exact RingEquiv.refl _

def heightFourQuotientEquiv (P : Ideal (TorusRing K)) [P.IsPrime]
    (hPid : P ≤ identityIdeal K) (hp : P.height = 4) (J : Ideal (TorusRing K)) :
    (Localization.AtPrime P ⧸ J.map
      (algebraMap (TorusRing K) (Localization.AtPrime P))) ≃+*
    (Localization.AtPrime (identityIdeal K) ⧸ J.map
      (algebraMap (TorusRing K) (Localization.AtPrime (identityIdeal K)))) := by
  have heq := prime_eq_identityIdeal_of_height_four P hPid hp
  subst P
  exact RingEquiv.refl _

theorem heightFour_quotient_length_eq_identity
    (P : Ideal (TorusRing K)) [P.IsPrime]
    (hPid : P ≤ identityIdeal K) (hp : P.height = 4) (J : Ideal (TorusRing K)) :
    Module.length (Localization.AtPrime P)
      (Localization.AtPrime P ⧸ J.map
        (algebraMap (TorusRing K) (Localization.AtPrime P))) =
    Module.length (Localization.AtPrime (identityIdeal K))
      (Localization.AtPrime (identityIdeal K) ⧸ J.map
        (algebraMap (TorusRing K) (Localization.AtPrime (identityIdeal K)))) := by
  have heq := prime_eq_identityIdeal_of_height_four P hPid hp
  subst P
  rfl

end SiegelZerosAwei.W21

end

end SiegelZeros

end OAI
