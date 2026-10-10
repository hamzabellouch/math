import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import OAI.NumberTheory.SiegelZeros.Structure.CanonicalDivisorScalars

namespace OAI

namespace SiegelZeros

noncomputable section
namespace WeightedTorusJets.GenericResidueFunctionField
open SiegelZeros.W58
open SiegelZerosAwei.Workers.W15

variable (k : Type*) [Field k] (p : Ideal (TorusRing k)) [p.IsPrime]

def genericResidueFunctionFieldEquiv :
    IsLocalRing.ResidueField (GenericLocalRing k p) ≃ₐ[TorusSubvarietyRing k p]
      (TorusSubvariety k p).functionField := by
  letI : IsFractionRing (TorusSubvarietyRing k p) (TorusSubvariety k p).functionField :=
    affineSpecFunctionField_isFractionRing (TorusSubvarietyRing k p)
  exact IsLocalization.algEquiv (nonZeroDivisors (TorusSubvarietyRing k p))
    (IsLocalRing.ResidueField (GenericLocalRing k p))
    (TorusSubvariety k p).functionField

@[simp] theorem genericResidueFunctionFieldEquiv_quotient (x : TorusSubvarietyRing k p) :
    genericResidueFunctionFieldEquiv k p
      (algebraMap (TorusSubvarietyRing k p)
        (IsLocalRing.ResidueField (GenericLocalRing k p)) x) =
      algebraMap (TorusSubvarietyRing k p) (TorusSubvariety k p).functionField x :=
  (genericResidueFunctionFieldEquiv k p).commutes x

theorem genericResidueFunctionFieldEquiv_base (x : TorusRing k) :
    genericResidueFunctionFieldEquiv k p
      (algebraMap (TorusRing k) (IsLocalRing.ResidueField (GenericLocalRing k p)) x) =
      algebraMap (TorusSubvarietyRing k p) (TorusSubvariety k p).functionField
        (Ideal.Quotient.mk p x) := by
  change genericResidueFunctionFieldEquiv k p
    (algebraMap (TorusSubvarietyRing k p)
      (IsLocalRing.ResidueField (GenericLocalRing k p)) (Ideal.Quotient.mk p x)) = _
  exact genericResidueFunctionFieldEquiv_quotient k p _

theorem genericResidueFunctionFieldEquiv_coordinate (i : Fin 4) :
    genericResidueFunctionFieldEquiv k p
      (algebraMap (TorusRing k) (IsLocalRing.ResidueField (GenericLocalRing k p))
        (coordinate k i)) = torusCoordinateFunction k p i :=
  genericResidueFunctionFieldEquiv_base k p (coordinate k i)

variable (P : Ideal (TorusRing ℂ)) [P.IsPrime]

local instance : Algebra ℂ (TorusSubvariety ℂ P).functionField := torusFunctionFieldAlgebra P
local instance : IsScalarTower ℂ (TorusSubvarietyRing ℂ P)
    (TorusSubvariety ℂ P).functionField :=
  IsScalarTower.of_algebraMap_eq' (R := ℂ) (S := TorusSubvarietyRing ℂ P)
    (A := (TorusSubvariety ℂ P).functionField) rfl

def genericResidueFunctionFieldAlgEquiv :
    IsLocalRing.ResidueField (GenericLocalRing ℂ P) ≃ₐ[ℂ]
      (TorusSubvariety ℂ P).functionField :=
  (genericResidueFunctionFieldEquiv ℂ P).restrictScalars ℂ

@[simp] theorem genericResidueFunctionFieldAlgEquiv_coordinate (i : Fin 4) :
    genericResidueFunctionFieldAlgEquiv P
      (algebraMap (TorusRing ℂ) (IsLocalRing.ResidueField (GenericLocalRing ℂ P))
        (coordinate ℂ i)) = torusCoordinateFunction ℂ P i :=
  genericResidueFunctionFieldEquiv_coordinate ℂ P i

@[simp] theorem genericResidueFunctionFieldAlgEquiv_scalar (c : ℂ) :
    genericResidueFunctionFieldAlgEquiv P
      (algebraMap ℂ (IsLocalRing.ResidueField (GenericLocalRing ℂ P)) c) =
        algebraMap ℂ (TorusSubvariety ℂ P).functionField c :=
  (genericResidueFunctionFieldAlgEquiv P).commutes c

end WeightedTorusJets.GenericResidueFunctionField

end

end SiegelZeros

end OAI
