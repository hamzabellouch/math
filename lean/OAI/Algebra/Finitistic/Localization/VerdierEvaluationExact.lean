import OAI.Algebra.Finitistic.Localization.TwoConeVerdier

namespace OAI
noncomputable section
open CategoryTheory Limits
namespace LittleFinitistic.TwoConeVerdier.ConePair
variable {C : Type*} [Category* C] [HasZeroObject C] [Preadditive C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsTriangulated C]
variable (T : ConePair C)
variable {D : Type*} [Category* D] [HasZeroObject D] [Preadditive D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
  [IsIso (F.map T.first.mor₁)] [IsIso (F.map T.second.mor₁)]

instance evaluationLift : Localization.Lifting T.q T.Sigma F (T.evaluation F) := by
  unfold evaluation
  infer_instance

instance evaluationShift : (T.evaluation F).CommShift ℤ :=
  Functor.commShiftOfLocalization T.q T.Sigma ℤ F (T.evaluation F)

instance evaluationFacShift : NatTrans.CommShift (T.evaluation_fac F).hom ℤ :=
  NatTrans.commShift_iso_hom_of_localization T.q T.Sigma ℤ F (T.evaluation F)

/-- The actual factor through the Verdier quotient is exact. -/
instance evaluationExact : (T.evaluation F).IsTriangulated := by
  let := Localization.essSurj_mapArrow_of_hasRightCalculusOfFractions T.q T.Sigma
  exact Functor.isTriangulated_of_precomp_iso (T.evaluation_fac F)

end LittleFinitistic.TwoConeVerdier.ConePair

end

end OAI
