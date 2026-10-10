import OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardAffine
import OAI.NumberTheory.PiExponent.Approximation.OpenBaseChange

namespace OAI

namespace PiExponent.CurveFinitePushforwardCoherent
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open CoherentAffineFinite FiniteGlobalPresentation ClosedPushforwardAffine
variable {X Y : Scheme.{0}}

private def presentationOfIso (X : Scheme.{0})
    {M N : SheafOfModules X.ringCatSheaf} (e : M ≅ N)
    (P : M.Presentation) : N.Presentation := by
  let : IsIso e.hom := e.isIso_hom
  exact P.ofIsIso e.hom

theorem affine_pushforward_sections_finite [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) [IsFinite f] (M : X.Modules) [M.IsQuasicoherent]
    (hM : LocallyFinitelyGenerated M) :
    Module.Finite Γ(Y,⊤) Γ((Scheme.Modules.pushforward f).obj M,⊤) := by
  have hfin : Module.Finite Γ(X,f ⁻¹ᵁ (⊤ : Y.Opens)) Γ(M,f ⁻¹ᵁ (⊤ : Y.Opens)) := by
    simpa only [Scheme.Hom.preimage_top] using! affine_sections_finite_of_localGenerators M hM
  let σ : Γ(Y,⊤) →+* Γ(X,f ⁻¹ᵁ (⊤ : Y.Opens)) := (f.app ⊤).hom
  let : Algebra Γ(Y,⊤) Γ(X,f ⁻¹ᵁ (⊤ : Y.Opens)) := σ.toAlgebra
  let : Module.Finite Γ(Y,⊤) Γ(X,f ⁻¹ᵁ (⊤ : Y.Opens)) :=
    f.finite_app ⊤ (isAffineOpen_top Y)
  let : Module Γ(Y,⊤) Γ(M,f ⁻¹ᵁ (⊤ : Y.Opens)) := Module.compHom _ σ
  let : IsScalarTower Γ(Y,⊤) Γ(X,f ⁻¹ᵁ (⊤ : Y.Opens)) Γ(M,f ⁻¹ᵁ (⊤ : Y.Opens)) :=
    IsScalarTower.of_compHom _ _ _
  have h := Module.Finite.trans (R := Γ(Y,⊤))
    Γ(X,f ⁻¹ᵁ (⊤ : Y.Opens)) Γ(M,f ⁻¹ᵁ (⊤ : Y.Opens))
  exact h

theorem affine_pushforward_exists_finitePresentation [IsAffine X] [IsAffine Y]
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [IsFinite f]
    (M : X.Modules) [M.IsQuasicoherent] (hM : LocallyFinitelyGenerated M) :
    ∃ P : ((Scheme.Modules.pushforward f).obj M).Presentation, P.IsFinite := by
  have := affine_pushforward_quasicoherent f M
  have := affine_pushforward_sections_finite f M hM
  exact affine_exists_finitePresentation_of_sections ((Scheme.Modules.pushforward f).obj M)

instance pushforward_isFinitePresentation (f : X ⟶ Y) [IsFinite f]
    [IsLocallyNoetherian Y] (M : X.Modules) [M.IsFinitePresentation] :
    ((Scheme.Modules.pushforward f).obj M).IsFinitePresentation := by
  let : M.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData M).choose.isQuasicoherent
  apply isFinitePresentation_of_affine_presentations
  intro U
  have : IsAffine U.1.toScheme := U.2
  have : IsAffine (f ⁻¹ᵁ U.1).toScheme := U.2.preimage f
  have hM := (locallyFinitelyGenerated_of_finitePresentation M).restrict (f ⁻¹ᵁ U.1).ι
  let : (M.restrict (f ⁻¹ᵁ U.1).ι).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_restrictFunctor (f ⁻¹ᵁ U.1).ι M
  obtain ⟨P,hP⟩ := affine_pushforward_exists_finitePresentation (f ∣_ U.1)
    (M.restrict (f ⁻¹ᵁ U.1).ι) hM
  exact ⟨presentationOfIso U.1.toScheme
    (PiExponentSeshadri.OpenBaseChange.iso f U.1 M).symm P,
    ⟨⟨hP.isFiniteType_generators.finite⟩, ⟨hP.isFiniteType_relations.finite⟩⟩⟩

end
end PiExponent.CurveFinitePushforwardCoherent

end OAI
