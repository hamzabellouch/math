import OAI.NumberTheory.PiExponent.Approximation.PushforwardTensor
import OAI.NumberTheory.PiExponent.Approximation.SectionOpens
import OAI.NumberTheory.PiExponent.Jets.CompactJetIdeal
import OAI.NumberTheory.PiExponent.LocalAlgebra.GlobalInvertibleIdeal

namespace OAI

noncomputable section
namespace PiExponent.InvertibleIdealAway
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.InvertibleLocal
variable {X B C : Scheme.{0}}

private theorem isIso_of_comp_iso_hom {D : Type*} [Category D]
    {A B C : D} (f : A ⟶ B) (e : B ≅ C) (h : IsIso (f ≫ e.hom)) : IsIso f :=
  (isIso_comp_right_iff f e.hom).mp h

theorem restrictedInclusion_isIso_of_unit
    (I : X.IdealSheafData) (p : B ⟶ X)
    (J : LineBundle B) (ι : J.sheaf ⟶ structureSheaf B)
    (hJ : PresentsPullbackIdeal I p J ι)
    (U : B.Opens) (V : X.affineOpens) (hUV : U ≤ p ⁻¹ᵁ V.1)
    (hunit : (I.comap p).comap U.ι = ⊤) :
    IsIso (restrictedInclusion J ι U.ι) := by
  have : Mono ι := hJ.1
  let φ := restrictedInclusion J ι U.ι
  have : Mono φ := inferInstance
  apply PiExponentSeshadri.IdealModule.isIso_of_affine_app
  intro W
  have himage : ((φ.val.app (op W.1)).hom).range = ⊤ := by
    change ((restrictedInclusion J ι U.ι).val.app (op W.1)).hom.range = _
    rw [restricted_image_on_chart J ι hJ U.ι W V
      ((U.ι_image_le W.1).trans hUV), hunit]
    rfl
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  constructor
  · have : Mono φ.val := inferInstanceAs
      (Mono ((Scheme.Modules.toPresheafOfModules U.toScheme).map φ))
    exact PresheafOfModules.injective_of_mono φ.val (op W.1)
  · intro r
    have hr : r ∈ ((φ.val.app (op W.1)).hom).range := by
      rw [himage]
      trivial
    exact hr

theorem inclusion_isIso_of_comap_top
    (I : X.IdealSheafData) (p : B ⟶ X)
    (J : LineBundle B) (ι : J.sheaf ⟶ structureSheaf B)
    (hJ : PresentsPullbackIdeal I p J ι) (hunit : I.comap p = ⊤) : IsIso ι := by
  apply PiExponentSeshadri.SectionOpens.isIso_of_locally_isIso
  intro b
  obtain ⟨V, hV, hbV, -⟩ := exists_isAffineOpen_mem_and_subset
    (show p b ∈ (⊤ : X.Opens) from trivial)
  let U := p ⁻¹ᵁ V
  have hi : IsIso (restrictedInclusion J ι U.ι) :=
    restrictedInclusion_isIso_of_unit I p J ι hJ U ⟨V, hV⟩ le_rfl (by
      rw [hunit, Scheme.IdealSheafData.comap_top])
  refine ⟨U, hbV, ?_⟩
  exact isIso_of_comp_iso_hom ((Scheme.Modules.restrictFunctor U.ι).map ι)
    (Scheme.Modules.restrictUnitIso U.ι) hi

theorem pullback_map_isIso_of_factors
    {M N : B.Modules} (ι : M ⟶ N) (g : C ⟶ B)
    (U : B.Opens) (h : C ⟶ U.toScheme) (hfac : h ≫ U.ι = g)
    [IsIso ((Scheme.Modules.restrictFunctor U.ι).map ι)] :
    IsIso ((Scheme.Modules.pullback g).map ι) := by
  have : IsIso ((Scheme.Modules.pullback U.ι).map ι) :=
    (NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorIsoPullback U.ι) ι).mp inferInstance
  have : IsIso ((Scheme.Modules.pullback h).map ((Scheme.Modules.pullback U.ι).map ι)) :=
    inferInstance
  have hcomp : IsIso ((Scheme.Modules.pullback (h ≫ U.ι)).map ι) :=
    (NatIso.isIso_map_iff (Scheme.Modules.pullbackComp h U.ι) ι).mp (by
      change IsIso ((Scheme.Modules.pullback h).map ((Scheme.Modules.pullback U.ι).map ι))
      infer_instance)
  exact hfac ▸ hcomp

theorem pullback_inclusion_isIso_of_avoids
    (I : X.IdealSheafData) (p : B ⟶ X)
    (J : LineBundle B) (ι : J.sheaf ⟶ structureSheaf B)
    (hJ : PresentsPullbackIdeal I p J ι) (g : C ⟶ B)
    (havoid : ∀ c, (g ≫ p) c ∉ I.support) :
    IsIso ((Scheme.Modules.pullback g).map ι) := by
  let V : X.Opens := ⟨(I.support : Set X)ᶜ, I.support.isClosed.isOpen_compl⟩
  let U : B.Opens := p ⁻¹ᵁ V
  have hunit : I.comap (U.ι ≫ p) = ⊤ :=
    CompactJetIdeal.restrict_eq_top_of_disjoint I (U.ι ≫ p) (fun u => u.property)
  have hpresent := presents_restrict_general I p J ι hJ U.ι
  have hinc : IsIso (restrictedInclusion J ι U.ι) :=
    inclusion_isIso_of_comap_top I (U.ι ≫ p) (restrictLineBundle J U.ι)
      (restrictedInclusion J ι U.ι) hpresent hunit
  have : IsIso ((Scheme.Modules.restrictFunctor U.ι).map ι) :=
    isIso_of_comp_iso_hom ((Scheme.Modules.restrictFunctor U.ι).map ι)
      (Scheme.Modules.restrictUnitIso U.ι) hinc
  have hrange : Set.range g ⊆ Set.range U.ι := by
    rintro _ ⟨c, rfl⟩
    exact ⟨⟨g c, havoid c⟩, rfl⟩
  let h : C ⟶ U.toScheme := IsOpenImmersion.lift U.ι g hrange
  exact pullback_map_isIso_of_factors ι g U h (IsOpenImmersion.lift_fac _ _ _)

def pullbackInclusion (J : LineBundle B) (ι : J.sheaf ⟶ structureSheaf B)
    (g : C ⟶ B) : (J.pullback g).sheaf ⟶ structureSheaf C :=
  (Scheme.Modules.pullback g).map ι ≫ (pullbackUnitIso g).hom

def pullbackIsoOfAvoids
    (I : X.IdealSheafData) (p : B ⟶ X)
    (J : LineBundle B) (ι : J.sheaf ⟶ structureSheaf B)
    (hJ : PresentsPullbackIdeal I p J ι) (g : C ⟶ B)
    (havoid : ∀ c, (g ≫ p) c ∉ I.support) :
    (J.pullback g).sheaf ≅ structureSheaf C := by
  exact @asIso C.Modules _ _ _ ((Scheme.Modules.pullback g).map ι)
    (pullback_inclusion_isIso_of_avoids I p J ι hJ g havoid) ≪≫ pullbackUnitIso g

def pullbackIsoOfComapTop
    (I : X.IdealSheafData) (p : B ⟶ X)
    (J : LineBundle B) (ι : J.sheaf ⟶ structureSheaf B)
    (hJ : PresentsPullbackIdeal I p J ι) (g : C ⟶ B)
    (hunit : I.comap (g ≫ p) = ⊤) :
    (J.pullback g).sheaf ≅ structureSheaf C := by
  apply pullbackIsoOfAvoids I p J ι hJ g
  intro c hc
  have hm : c ∈ (I.comap (g ≫ p)).support := by
    rw [Scheme.IdealSheafData.support_comap]
    exact hc
  rw [hunit] at hm
  exact hm

end PiExponent.InvertibleIdealAway

end

end OAI
