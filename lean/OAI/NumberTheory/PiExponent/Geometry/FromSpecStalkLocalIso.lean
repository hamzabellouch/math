import Mathlib.AlgebraicGeometry.Stalk

namespace OAI

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace PiExponent

universe u

theorem specMap_stalkMap_isIso_of_isLocalization
    (R S : CommRingCat.{u}) [Algebra R S] (M : Submonoid R)
    [IsLocalization M S] (y : Spec S) :
    IsIso ((Spec.map (CommRingCat.ofHom (algebraMap R S))).stalkMap y) := by
  let e := IsLocalization.algEquiv M (Localization M) S
  have he : IsIso (CommRingCat.ofHom e.toRingHom) :=
    inferInstanceAs (IsIso e.toRingEquiv.toCommRingCatIso.hom)
  have hmap : IsIso (Spec.map (CommRingCat.ofHom e.toRingHom)) := inferInstance
  have hstalk : IsIso ((Spec.map (CommRingCat.ofHom e.toRingHom)).stalkMap y) :=
    inferInstance
  have h : Spec.map (CommRingCat.ofHom (algebraMap R S)) =
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (Localization M))) := by
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact e.toAlgHom.comp_algebraMap.symm
  rw [h, Scheme.Hom.stalkMap_comp]
  have hloc : IsIso ((Spec.map (CommRingCat.ofHom
      (algebraMap R (Localization M)))).stalkMap
        (Spec.map (CommRingCat.ofHom e.toRingHom) y)) :=
    isIso_SpecMap_stakMap_localization R M _
  exact (asIso ((Spec.map (CommRingCat.ofHom
      (algebraMap R (Localization M)))).stalkMap
        (Spec.map (CommRingCat.ofHom e.toRingHom) y)) ≪≫
    asIso ((Spec.map (CommRingCat.ofHom e.toRingHom)).stalkMap y)).isIso_hom

instance fromSpecStalk_stalkMap_isIso (X : Scheme.{u}) (x : X)
    (y : Spec (X.presheaf.stalk x)) :
    IsIso ((X.fromSpecStalk x).stalkMap y) := by
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (TopologicalSpace.Opens.mem_top x)
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hxU, IsAffineOpen.fromSpecStalk,
    Scheme.Hom.stalkMap_comp]
  let : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    (X.presheaf.germ U x hxU).hom.toAlgebra
  have := hU.isLocalization_stalk ⟨x, hxU⟩
  have : IsIso ((Spec.map (X.presheaf.germ U x hxU)).stalkMap y) :=
    specMap_stalkMap_isIso_of_isLocalization Γ(X, U) (X.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl y
  exact (asIso (hU.fromSpec.stalkMap ((Spec.map (X.presheaf.germ U x hxU)) y)) ≪≫
    asIso ((Spec.map (X.presheaf.germ U x hxU)).stalkMap y)).isIso_hom

def fromSpecStalkStalkIso (X : Scheme.{u}) (x : X)
    (y : Spec (X.presheaf.stalk x)) :
    X.presheaf.stalk (X.fromSpecStalk x y) ≅
      (Spec (X.presheaf.stalk x)).presheaf.stalk y :=
  asIso ((X.fromSpecStalk x).stalkMap y)

end PiExponent

end

end OAI
