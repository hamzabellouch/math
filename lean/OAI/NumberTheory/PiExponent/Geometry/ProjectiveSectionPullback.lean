import OAI.NumberTheory.PiExponent.Approximation.ClosedRestrictionTensor
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionExtension

namespace OAI

noncomputable section
namespace PiExponent.ProjectiveSectionExtension
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
open PiExponent.GeometrySupport
variable {X Y : Scheme.{0}}

def globalPushEquiv (f : X ⟶ Y) (M : X.Modules) :
    GlobalSections X M ≃ GlobalSections Y ((Scheme.Modules.pushforward f).obj M) :=
  Equiv.ofBijective (fun s => PiExponentSeshadri.IdealModule.structureMap f ≫
    (Scheme.Modules.pushforward f).map s)
    (ClosedImmersionSerreTransfer.globalHom_push_bijective f M)

def quotientPowerIso (L : LineBundle Y) (f : X ⟶ Y) (n : ℕ) :
    (moduleTwistFunctor L n).obj ((Scheme.Modules.pushforward f).obj (structureSheaf X)) ≅
      (Scheme.Modules.pushforward f).obj (modulePow X (L.pullback f).sheaf n) :=
  (ProjectionFormula.twistIso f (structureSheaf X) L n).symm ≪≫
    (Scheme.Modules.pushforward f).mapIso (moduleTwistUnitIso (L.pullback f) n)

def quotientSectionsEquiv (L : LineBundle Y) (f : X ⟶ Y) (n : ℕ) :
    GlobalSections Y ((moduleTwistFunctor L n).obj
      ((Scheme.Modules.pushforward f).obj (structureSheaf X))) ≃
    GlobalSections X (modulePow X (L.pullback f).sheaf n) :=
  (Iso.homCongr (Iso.refl (structureSheaf Y)) (quotientPowerIso L f n)).trans
    (globalPushEquiv f _).symm

theorem quotientSectionsEquiv_restriction (L : LineBundle Y) (f : X ⟶ Y)
    (n : ℕ) (s : GlobalSections Y (modulePow Y L.sheaf n)) :
    quotientSectionsEquiv L f n (quotientPowerRestriction L f n s) =
      pullbackPowerSection L f n s := by
  apply (globalPushEquiv f _).injective
  change globalPushEquiv f _ ((globalPushEquiv f _).symm
    (quotientPowerRestriction L f n s ≫ (quotientPowerIso L f n).hom)) = _
  rw [Equiv.apply_symm_apply]
  change (s ≫ (moduleTwistUnitIso L n).inv ≫
    (moduleTwistFunctor L n).map (PiExponentSeshadri.IdealModule.structureMap f)) ≫
      (ProjectionFormula.twistIso f (structureSheaf X) L n).inv ≫
        (Scheme.Modules.pushforward f).map (moduleTwistUnitIso (L.pullback f) n).hom = _
  change _ = PiExponentSeshadri.IdealModule.structureMap f ≫
    (Scheme.Modules.pushforward f).map (pullbackPowerSection L f n s)
  erw [Category.assoc, Category.assoc]
  simpa only [PiExponentSeshadri.Frames.O, structureSheaf,
    PiExponentSeshadri.IdealModule.unit] using! ClosedRestrictionTensor.section_restriction_eq f L n s

theorem eventual_projective_pullbackPowerSection_surjective
    {R σ : Type} [CommRing R] [IsNoetherianRing R] [Fintype σ] [Nonempty σ]
    (f : X ⟶ ProjectiveO1.projectiveSpace R σ) [IsClosedImmersion f] :
    ∃ N, ∀ n, N ≤ n → Function.Surjective
      (pullbackPowerSection (ProjectiveO1.lineBundle (R := R) (σ := σ)) f n) := by
  obtain ⟨N, hN⟩ := eventual_projective_quotientPowerRestriction_surjective f
  refine ⟨N, fun n hn t => ?_⟩
  obtain ⟨s, hs⟩ := hN n hn ((quotientSectionsEquiv _ f n).symm t)
  refine ⟨s, ?_⟩
  rw [← quotientSectionsEquiv_restriction, hs, Equiv.apply_symm_apply]

theorem eventual_projective_homogeneous_extension
    {R σ : Type} [CommRing R] [IsNoetherianRing R] [Fintype σ] [Nonempty σ]
    (f : X ⟶ ProjectiveO1.projectiveSpace R σ) [IsClosedImmersion f] :
    ∃ N, ∀ n, N ≤ n →
      ∀ t : GlobalSections X (modulePow X
        ((ProjectiveO1.lineBundle (R := R) (σ := σ)).pullback f).sheaf n),
      ∃ s : GlobalSections (ProjectiveO1.projectiveSpace R σ)
          (modulePow _ (ProjectiveO1.lineBundle (R := R) (σ := σ)).sheaf n),
        ∃ p : MvPolynomial.homogeneousSubmodule σ R n,
          pullbackPowerSection (ProjectiveO1.lineBundle (R := R) (σ := σ)) f n s = t ∧
          ∀ i, PiExponentSeshadri.Projective.dehomogenize i p.val =
            ProjectiveO1.globalSectionChartPolynomial n i s := by
  obtain ⟨N, hN⟩ := eventual_projective_pullbackPowerSection_surjective f
  refine ⟨N, fun n hn t => ?_⟩
  obtain ⟨s, hs⟩ := hN n hn t
  obtain ⟨p, hp, _⟩ := ProjectiveO1.globalSection_homogeneous_polynomial n s
  exact ⟨s, p, hs, hp⟩

end PiExponent.ProjectiveSectionExtension
end

end OAI
