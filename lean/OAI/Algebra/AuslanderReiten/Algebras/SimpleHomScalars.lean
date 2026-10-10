import OAI.Algebra.AuslanderReiten.Fibers.FiberFullHomCoordinates
import OAI.Algebra.AuslanderReiten.HomComplex.FullHomShiftedIdentity

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open CochainComplex.HomComplex CompleteComparison
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "HC" => HomotopyCategory (ModuleCat (A k q)) (ComplexShape.up ℤ)

def simpleZeroScalarEquiv (hq1 : 1+q ≠ 0) : SimpleHom q 0 ≃ₗ[k] k :=
  (simpleFullHomEquiv q 0).symm.trans (A.fullHomZeroScalarEquiv q hq1)

def simpleZeroUnit : SimpleHom q 0 :=
  (shiftFunctorZero HC ℤ).inv.app (simpleHomotopyObject q)

theorem simpleZeroScalarEquiv_unit (hq1 : 1+q ≠ 0) :
    simpleZeroScalarEquiv q hq1 (simpleZeroUnit q) = 1 := by
  have h := fullHomShiftedHomotopyEquiv_identity k (A.simpleComplete q)
  change simpleFullHomEquiv q 0 (fullHomIdentity (A.simpleComplete q)) = simpleZeroUnit q at h
  change A.fullHomZeroScalarEquiv q hq1 ((simpleFullHomEquiv q 0).symm (simpleZeroUnit q)) = 1
  rw [← h, LinearEquiv.symm_apply_apply]
  exact A.fullHomZeroScalarEquiv_identity q hq1

theorem simpleHom_eq_scalar_unit (hq1 : 1+q ≠ 0) (v : SimpleHom q 0) :
    v = simpleZeroScalarEquiv q hq1 v • simpleZeroUnit q := by
  apply (simpleZeroScalarEquiv q hq1).injective
  rw [map_smul, simpleZeroScalarEquiv_unit]
  exact (mul_one _).symm

omit [CharP k 2] in
theorem simpleZeroUnit_postcomp {Y : HC} (g : simpleHomotopyObject q ⟶ Y) :
    simpleZeroUnit q ≫ g⟦(0 : ℤ)⟧' = g ≫ (shiftFunctorZero HC ℤ).inv.app Y :=
  ((shiftFunctorZero HC ℤ).inv.naturality g).symm

end ArExplicit.T

end

end OAI
