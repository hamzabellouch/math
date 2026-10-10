import OAI.AlgebraicGeometry.SurfaceCones.KummerProjCover
import OAI.AlgebraicGeometry.SurfaceCones.CotangentSheaf

namespace OAI

/-! The normalized projective surface is smooth over ℂ. -/
noncomputable section
namespace SourceSymmetry
open ExplicitCone AlgebraicGeometry CategoryTheory

lemma homogeneousAway_toComplex (c : L) (hc : c ∈ pieces 1) :
    Proj.awayι grading (SectionCompletion.linearSection pieces c hc)
      (SectionCompletion.linearSection_homogeneous pieces c hc)
      (by norm_num : 0 < (1 : ℕ)) ≫ projectiveSurfaceToComplex =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ
        (SectionCompletion.homogeneousChart pieces c hc))) := by
  unfold projectiveSurfaceToComplex
  erw [← Category.assoc]
  erw [Proj.awayι_toSpecZero grading (SectionCompletion.linearSection pieces c hc)
    (SectionCompletion.linearSection_homogeneous pieces c hc) (by norm_num : 0 < (1 : ℕ))]
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  rfl

lemma projAway_toComplex (t : SectionIndex) :
    Proj.awayι grading (projSection t)
      (SectionCompletion.linearSection_homogeneous pieces _ _)
      (by norm_num : 0 < (1 : ℕ)) ≫ projectiveSurfaceToComplex =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (projChart t))) :=
  homogeneousAway_toComplex (sectionCoefficient t) (sectionCoefficient_mem_piece t)

lemma projOpen_toComplex_smooth (t : SectionIndex) (ht : Good t) :
    Smooth ((Proj.basicOpen grading (projSection t)).ι ≫ projectiveSurfaceToComplex) := by
  let hs : IsZariskiLocalAtSource (@AlgebraicGeometry.Smooth.{0}) :=
    @HasRingHomProperty.instIsZariskiLocalAtSource (@AlgebraicGeometry.Smooth.{0})
      (@RingHom.Smooth) inferInstance
  let : MorphismProperty.RespectsIso (@AlgebraicGeometry.Smooth.{0}) := hs.toRespects
  let e := Proj.basicOpenIsoSpec grading (projSection t)
    (SectionCompletion.linearSection_homogeneous pieces _ _)
    (by norm_num : 0 < (1 : ℕ))
  have h : Smooth (e.inv ≫ (Proj.basicOpen grading (projSection t)).ι ≫
      projectiveSurfaceToComplex) := by
    erw [← Category.assoc]
    change Smooth (Proj.awayι grading (projSection t) _ _ ≫ projectiveSurfaceToComplex)
    rw [projAway_toComplex]
    rw [HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Smooth.{0})]
    change RingHom.Smooth (algebraMap ℂ (projChart t))
    exact RingHom.smooth_algebraMap.mpr (projChart_smooth t ht)
  exact (MorphismProperty.cancel_left_of_respectsIso @AlgebraicGeometry.Smooth.{0} e.inv _).mp h

/-- The Proj of the normalized section algebra is smooth over ℂ. -/
theorem projectiveSurface_smooth : Smooth projectiveSurfaceToComplex := by
  let hs : IsZariskiLocalAtSource (@AlgebraicGeometry.Smooth.{0}) :=
    @HasRingHomProperty.instIsZariskiLocalAtSource (@AlgebraicGeometry.Smooth.{0})
      (@RingHom.Smooth) inferInstance
  apply IsZariskiLocalAtSource.of_iSup_eq_top smoothOpen smoothOpen_cover
  intro t
  exact projOpen_toComplex_smooth t.val t.property

end SourceSymmetry


/-! Affine descriptions of the cotangent sheaf on the smooth coefficient charts. -/
open CategoryTheory AlgebraicGeometry
namespace SourceSymmetry
open ExplicitCone

/-- The coefficient charts are open immersions into the source Proj. -/
def coefficientIota (t : SectionIndex) (ht : Good t) :
    Spec (CommRingCat.of (coefficientChart t)) ⟶ projectiveSurface :=
  (projOpenIso t ht).inv ≫ (Proj.basicOpen grading (projSection t)).ι

instance coefficientIota_open (t : SectionIndex) (ht : Good t) :
    IsOpenImmersion (coefficientIota t ht) := by
  dsimp [coefficientIota]
  refine @IsOpenImmersion.comp _ _ _ _ _ ?_ ?_
  · infer_instance
  · change IsOpenImmersion ((Proj grading).ofRestrict
      (Proj.basicOpen grading (projSection t)).isOpenEmbedding)
    infer_instance

lemma coefficientIota_toComplex (t : SectionIndex) (ht : Good t) :
    coefficientIota t ht ≫ projectiveSurfaceToComplex =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (coefficientChart t))) := by
  change (Spec.map (CommRingCat.ofHom (projChartEquiv t ht).toRingHom) ≫
    Proj.awayι grading (projSection t) _ _) ≫ projectiveSurfaceToComplex = _
  erw [Category.assoc,projAway_toComplex,← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact (projChartEquiv t ht).toAlgHom.comp_algebraMap

/-- The intrinsic source cotangent sheaf on each good chart is the Kähler differential module already used in the canonical-frame calculation. -/
def coefficientCotangentIso (t : SectionIndex) (ht : Good t) :
    (ActualCotangent.sheaf projectiveSurfaceToComplex).restrict (coefficientIota t ht) ≅
      @tilde (CommRingCat.of (coefficientChart t))
        (ActualCotangent.affineModule (k := ℂ) (coefficientChart t)) :=
  ActualCotangent.openAffineIso projectiveSurfaceToComplex (coefficientChart t)
    (coefficientIota t ht) (coefficientIota_toComplex t ht)

end SourceSymmetry

end

end OAI
