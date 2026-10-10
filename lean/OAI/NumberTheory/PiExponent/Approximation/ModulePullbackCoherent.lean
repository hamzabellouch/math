import OAI.NumberTheory.PiExponent.Approximation.FramedPullback
import OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponent.FiniteGlobalPresentation

private def presentationOfIso (X : Scheme.{0})
    {M N : SheafOfModules X.ringCatSheaf} (e : M ≅ N)
    (P : M.Presentation) : N.Presentation := by
  let : IsIso e.hom := e.isIso_hom
  exact P.ofIsIso e.hom

theorem pullback_isFinitePresentation {X Y : Scheme.{0}} (f : Y ⟶ X)
    (M : X.Modules) [M.IsFinitePresentation] :
    ((Scheme.Modules.pullback f).obj M).IsFinitePresentation := by
  apply isFinitePresentation_of_localPresentations
  intro y
  obtain ⟨U, hy, P, hP⟩ := exists_local_finitePresentation M (f y)
  let F : SheafOfModules U.toScheme.ringCatSheaf ⥤
      SheafOfModules (f ⁻¹ᵁ U).toScheme.ringCatSheaf :=
    Scheme.Modules.pullback (f ∣_ U)
  let : PreservesColimitsOfSize.{0,0} F :=
    (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).leftAdjoint_preservesColimits
  let Q := P.map F (pullbackUnitIso (f ∣_ U)).symm
  let e := (pullbackRestrictNatIso f U).app M
  exact ⟨f ⁻¹ᵁ U, hy, presentationOfIso (f ⁻¹ᵁ U).toScheme e.symm Q,
    ⟨⟨hP.isFiniteType_generators.finite⟩, ⟨hP.isFiniteType_relations.finite⟩⟩⟩

end
end PiExponentSeshadri.Geometry

end OAI
