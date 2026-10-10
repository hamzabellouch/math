import OAI.Algebra.Finitistic.Ordinary.OrdinaryShiftSign
import Mathlib.CategoryTheory.Preadditive.FunctorCategory

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.BimoduleTotal
universe u v
variable (C : Type u) [Category.{v} C] [Preadditive C]

def signedShiftIso (a s : ℤ) :
    shiftFunctor (CochainComplex C ℤ) s ⋙ shiftFunctor _ a ≅
      shiftFunctor (CochainComplex C ℤ) a ⋙ shiftFunctor _ s :=
  OrdinarySimulation.integerUnitIso _ (a*s).negOnePow ≪≫ shiftFunctorComm _ s a

theorem signedShiftIso_hom_f (a s n : ℤ) (K : CochainComplex C ℤ) :
    ((signedShiftIso C a s).hom.app K).f n =
      (a*s).negOnePow • (K.XIsoOfEq (show n+a+s=n+s+a by omega)).hom := by
  simp [signedShiftIso,OrdinarySimulation.integerUnitIso,
    CochainComplex.shiftFunctorComm_hom_app_f]

/-- The standard signed commutation structure for a cochain shift. -/
@[instance_reducible]
def signedShiftComm (a : ℤ) : (shiftFunctor (CochainComplex C ℤ) a).CommShift ℤ where
  commShiftIso s := signedShiftIso C a s
  commShiftIso_zero := by
    ext K n
    simp [signedShiftIso_hom_f,Functor.CommShift.isoZero,
      CochainComplex.shiftFunctorZero_hom_app_f,CochainComplex.shiftFunctorZero_inv_app_f,
      HomologicalComplex.XIsoOfEq]
  commShiftIso_add s t := by
    ext K n
    simp [signedShiftIso_hom_f,Functor.CommShift.isoAdd_hom_app,
      CochainComplex.shiftFunctorAdd_hom_app_f,CochainComplex.shiftFunctorAdd_inv_app_f,
      CochainComplex.shiftFunctor_map_f',HomologicalComplex.XIsoOfEq,
      Linear.units_smul_comp,Linear.comp_units_smul,smul_smul,
      ← Int.negOnePow_add,mul_add]
end LittleFinitistic.BimoduleTotal

end

end OAI
