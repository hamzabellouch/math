import OAI.NumberTheory.PiExponent.Ampleness.ClosedAmpleRestriction
import OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardCoherent
import OAI.NumberTheory.PiExponent.Approximation.SerreSectionLifting
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveGlobalPolynomials
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveSpaceSerre
import OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule

namespace OAI

namespace PiExponent.ProjectiveSectionExtension
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open PiExponentSeshadri.Geometry
open GeometrySupport

variable {X Y : Scheme.{0}}

def quotientPowerRestriction (L : LineBundle Y) (f : X ⟶ Y) (n : ℕ)
    (s : GlobalSections Y (modulePow Y L.sheaf n)) :
    GlobalSections Y ((moduleTwistFunctor L n).obj
      ((Scheme.Modules.pushforward f).obj (structureSheaf X))) :=
  s ≫ (moduleTwistUnitIso L n).inv ≫
    (moduleTwistFunctor L n).map (PiExponentSeshadri.IdealModule.structureMap f)

lemma idealModule_isFinitePresentation [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsClosedImmersion f] :
    (PiExponentSeshadri.IdealModule.idealModule f).IsFinitePresentation := by
  let : (PiExponentSeshadri.IdealModule.unit X).IsFinitePresentation :=
    LineBundleCoherent.structureSheaf_isFinitePresentation
  let : (PiExponentSeshadri.IdealModule.unit Y).IsFinitePresentation :=
    LineBundleCoherent.structureSheaf_isFinitePresentation
  let : ((Scheme.Modules.pushforward f).obj
      (PiExponentSeshadri.IdealModule.unit X)).IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
      ((Scheme.Modules.pushforward f).obj
        (PiExponentSeshadri.IdealModule.unit X))).choose.isQuasicoherent
  exact FiniteGlobalPresentation.kernel_isFinitePresentation
    (PiExponentSeshadri.IdealModule.structureMap f)

theorem quotientPowerRestriction_surjective_of_h1_zero
    (L : LineBundle Y) (f : X ⟶ Y) [IsClosedImmersion f] (n : ℕ)
    (hzero : ∀ x : cohomology
      ((moduleTwistFunctor L n).obj (PiExponentSeshadri.IdealModule.idealModule f)) 1, x = 0) :
    Function.Surjective (quotientPowerRestriction L f n) := by
  let S := ShortComplex.mk (PiExponentSeshadri.IdealModule.inclusion f)
    (PiExponentSeshadri.IdealModule.structureMap f) (kernel.condition _)
  have hS : S.ShortExact := PiExponentSeshadri.IdealModule.closedSequence_exact f
  have hsurj := SerreSectionLifting.globalSections_surjective_of_h1_zero
    (S.map (moduleTwistFunctor L n)) (moduleTwistFunctor_shortExact L n S hS) hzero
  intro s
  obtain ⟨t, ht⟩ := hsurj s
  refine ⟨t ≫ (moduleTwistUnitIso L n).hom, ?_⟩
  change t ≫ (moduleTwistFunctor L n).map
    (PiExponentSeshadri.IdealModule.structureMap f) = s at ht
  change (t ≫ (moduleTwistUnitIso L n).hom) ≫ (moduleTwistUnitIso L n).inv ≫ _ = s
  erw [Category.assoc, Iso.hom_inv_id_assoc]
  exact ht

theorem eventual_projective_quotientPowerRestriction_surjective
    {R σ : Type} [CommRing R] [IsNoetherianRing R] [Fintype σ] [Nonempty σ]
    (f : X ⟶ ProjectiveO1.projectiveSpace R σ) [IsClosedImmersion f] :
    ∃ N, ∀ n, N ≤ n → Function.Surjective
      (quotientPowerRestriction (ProjectiveO1.lineBundle (R := R) (σ := σ)) f n) := by
  let := idealModule_isFinitePresentation f
  obtain ⟨N, hN⟩ := ProjectiveO1.serre_vanishing R σ
    (PiExponentSeshadri.IdealModule.idealModule f)
  exact ⟨N, fun n hn => quotientPowerRestriction_surjective_of_h1_zero
    (ProjectiveO1.lineBundle (R := R) (σ := σ)) f n (hN n hn 1 (by decide))⟩

end
end PiExponent.ProjectiveSectionExtension

end OAI
