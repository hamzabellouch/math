import OAI.AlgebraicGeometry.SurfaceCones.AffineFrameSection

namespace OAI

open _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry in
private local instance canonicalSectionModule {X : Scheme.{_}}
    (M : X.Modules) (U : X.Opens) : Module Γ(X,U) (M.val.obj (.op U)) :=
  (M.val.obj (.op U)).isModule

open _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry CategoryTheory in
private local instance tensorSectionModule {C : Type*} [Category C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat)
    (M : SheafOfModules (ActualSheafTensor.ringSheaf R)) (U : Cᵒᵖ) :
    Module (R.obj.obj U) (M.val.obj U) :=
  (M.val.obj U).isModule

open _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry CategoryTheory Opposite in
private local instance schemeObjectSMul {X : Scheme.{_}} (U : X.Opens)
    (M : ModuleCat (X.ringCatSheaf.obj.obj (op U))) : SMul Γ(X,U) M :=
  M.isModule.toSMul

open _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry CategoryTheory in
private local instance tensorObjectSMul {C : Type*} [Category C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat) (U : Cᵒᵖ)
    (M : ModuleCat ((ActualSheafTensor.ringSheaf R).obj.obj U)) : SMul (R.obj.obj U) M :=
  M.isModule.toSMul

open _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry CategoryTheory Opposite in
private local instance schemeRestrictionHSMul {X : Scheme.{_}} {U V : X.Opens}
    (h : V ≤ U) (M : ModuleCat (X.ringCatSheaf.obj.obj (op V))) :
    HSMul Γ(X,V)
      ((ModuleCat.restrictScalars (X.ringCatSheaf.obj.map (homOfLE h).op).hom).obj M)
      ((ModuleCat.restrictScalars (X.ringCatSheaf.obj.map (homOfLE h).op).hom).obj M) :=
  ⟨fun a m => @SMul.smul _ _ M.isModule.toSMul a m⟩

noncomputable section
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite _root_.HomogeneousLocalization _root_.OAI.HomogeneousLocalization
namespace SourcePullbackChart
open ExplicitCone SectionCompletion Scheme.Modules ActualSections

/-- Degree-one section ratios in the normalized section algebra. -/
lemma source_degreeOne_ratio {g c : polynomials pieces}
    (hg : g ∈ homogeneous pieces 1) (hc : c ∈ homogeneous pieces 1)
    {M : (Proj (homogeneous pieces)).Modules}
    (s t : SheafOfModules.unit (Proj (homogeneous pieces)).ringCatSheaf ⟶ M)
    (u : Fin 3 → (SheafOfModules.unit (Proj (homogeneous pieces)).ringCatSheaf ⟶ M))
    (hs : ∀ i, (restrictUnitIso (Proj.awayι (homogeneous pieces)
          (linearSection pieces (projectiveParameter i) (projectiveParameter_mem i))
          (linearSection_homogeneous pieces (projectiveParameter i) (projectiveParameter_mem i))
          (by decide : 0 < 1))).inv ≫
        (restrictFunctor (Proj.awayι (homogeneous pieces)
          (linearSection pieces (projectiveParameter i) (projectiveParameter_mem i))
          (linearSection_homogeneous pieces (projectiveParameter i) (projectiveParameter_mem i))
          (by decide : 0 < 1))).map s =
      scalar ((Scheme.ΓSpecIso (.of (Away (homogeneous pieces)
          (linearSection pieces (projectiveParameter i) (projectiveParameter_mem i))))).inv (Proj.degreeOneFraction (homogeneous pieces)
          (linearSection_homogeneous pieces (projectiveParameter i) (projectiveParameter_mem i)) hc)) ≫
        (restrictUnitIso (Proj.awayι (homogeneous pieces)
          (linearSection pieces (projectiveParameter i) (projectiveParameter_mem i))
          (linearSection_homogeneous pieces (projectiveParameter i) (projectiveParameter_mem i))
          (by decide : 0 < 1))).inv ≫
        (restrictFunctor (Proj.awayι (homogeneous pieces)
          (linearSection pieces (projectiveParameter i) (projectiveParameter_mem i))
          (linearSection_homogeneous pieces (projectiveParameter i) (projectiveParameter_mem i))
          (by decide : 0 < 1))).map (u i))
    (ht : ∀ i, (restrictUnitIso (Proj.awayι (homogeneous pieces)
          (linearSection pieces (projectiveParameter i) (projectiveParameter_mem i))
          (linearSection_homogeneous pieces (projectiveParameter i) (projectiveParameter_mem i))
          (by decide : 0 < 1))).inv ≫
        (restrictFunctor (Proj.awayι (homogeneous pieces)
          (linearSection pieces (projectiveParameter i) (projectiveParameter_mem i))
          (linearSection_homogeneous pieces (projectiveParameter i) (projectiveParameter_mem i))
          (by decide : 0 < 1))).map t =
      scalar ((Scheme.ΓSpecIso (.of (Away (homogeneous pieces)
          (linearSection pieces (projectiveParameter i) (projectiveParameter_mem i))))).inv (Proj.degreeOneFraction (homogeneous pieces)
          (linearSection_homogeneous pieces (projectiveParameter i) (projectiveParameter_mem i)) hg)) ≫
        (restrictUnitIso (Proj.awayι (homogeneous pieces)
          (linearSection pieces (projectiveParameter i) (projectiveParameter_mem i))
          (linearSection_homogeneous pieces (projectiveParameter i) (projectiveParameter_mem i))
          (by decide : 0 < 1))).inv ≫
        (restrictFunctor (Proj.awayι (homogeneous pieces)
          (linearSection pieces (projectiveParameter i) (projectiveParameter_mem i))
          (linearSection_homogeneous pieces (projectiveParameter i) (projectiveParameter_mem i))
          (by decide : 0 < 1))).map (u i)) :
    (restrictUnitIso (Proj.awayι (homogeneous pieces) g hg (by decide : 0 < 1))).inv ≫
        (restrictFunctor (Proj.awayι (homogeneous pieces) g hg (by decide : 0 < 1))).map s =
      scalar ((Scheme.ΓSpecIso (.of (Away (homogeneous pieces) g))).inv
        (Proj.degreeOneFraction (homogeneous pieces) hg hc)) ≫
        (restrictUnitIso (Proj.awayι (homogeneous pieces) g hg (by decide : 0 < 1))).inv ≫
        (restrictFunctor (Proj.awayι (homogeneous pieces) g hg (by decide : 0 < 1))).map t := by
  have hcover : (⨆ i : Fin 3,
      (Proj.awayι (homogeneous pieces)
        (linearSection pieces (projectiveParameter i) (projectiveParameter_mem i))
        (linearSection_homogeneous pieces (projectiveParameter i) (projectiveParameter_mem i))
        (by decide : 0 < 1)).opensRange) = ⊤ := surfaceIota_cover
  exact Proj.degreeOne_section_ratio (homogeneous pieces)
    (fun i : Fin 3 => linearSection pieces (projectiveParameter i) (projectiveParameter_mem i))
    (fun i => linearSection_homogeneous pieces (projectiveParameter i) (projectiveParameter_mem i))
    hcover hg hc s t u hs ht

end SourcePullbackChart

/-! Conormal ratios on homogeneous degree-one charts. -/
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite _root_.HomogeneousLocalization _root_.OAI.HomogeneousLocalization
namespace SourcePullbackChart
open ExplicitCone KummerSourceModel SourceZeroSections SectionCompletion
  Scheme.Modules ActualCartier ActualSections
attribute [local instance] integralSurfaceCommRing integralSurfaceSemiring
  integralPullbackCommRing integralPullbackSemiring pullbackBaseAlgebra surfaceOriginAlgebra
  completedPullbackModule completedPullbackAction completedPullbackSMul completedPullbackTower
  completedSurfaceModule completedSeriesModule completedSourceChartCommRing completedSourceChartSemiring
  completedSourceAlgebra

lemma degreeOneCoefficient_fraction (i : Fin 3) (c : L) (hc : c ∈ pieces 1) :
    degreeOneCoefficient i c hc = Proj.degreeOneFraction (homogeneous pieces)
      (linearSection_homogeneous pieces (projectiveParameter i) (projectiveParameter_mem i))
      (linearSection_homogeneous pieces c hc) :=
  dehomogenize_linearSection pieces (projectiveParameter i) (projectiveParameter_mem i)
    (projectiveParameter_ne_zero i) c hc

lemma degreeOneConormalFraction_ratio (i : Fin 3) (c : L) (hc : c ∈ pieces 1) :
    degreeOneConormalChartSection i c hc =
      scalar ((Scheme.ΓSpecIso (.of (surfaceChart i))).inv
        (Proj.degreeOneFraction (homogeneous pieces)
          (linearSection_homogeneous pieces (projectiveParameter i) (projectiveParameter_mem i))
          (linearSection_homogeneous pieces c hc))) ≫
        degreeOneConormalChartSection i (projectiveParameter i) (projectiveParameter_mem i) := by
  exact (degreeOneConormalChartSection_ratio i c hc).trans
    (congrArg (fun a => scalar ((Scheme.ΓSpecIso (.of (surfaceChart i))).inv a) ≫
      degreeOneConormalChartSection i (projectiveParameter i) (projectiveParameter_mem i))
        (degreeOneCoefficient_fraction i c hc))

lemma degreeOne_projective_ratio_template {M : projectiveSurface.Modules}
    (G : ∀ (c : L), c ∈ pieces 1 → (SheafOfModules.unit projectiveSurface.ringCatSheaf ⟶ M))
    (hG : ∀ (i : Fin 3) (c : L) (hc : c ∈ pieces 1),
      (restrictUnitIso (surfaceIota i)).inv ≫ (restrictFunctor (surfaceIota i)).map (G c hc) =
        scalar ((Scheme.ΓSpecIso (.of (surfaceChart i))).inv
          (Proj.degreeOneFraction (homogeneous pieces)
            (linearSection_homogeneous pieces (projectiveParameter i) (projectiveParameter_mem i))
            (linearSection_homogeneous pieces c hc))) ≫
          (restrictUnitIso (surfaceIota i)).inv ≫ (restrictFunctor (surfaceIota i)).map
            (G (projectiveParameter i) (projectiveParameter_mem i)))
    (c d : L) (hc : c ∈ pieces 1) (hd : d ∈ pieces 1) :
    (restrictUnitIso (Proj.awayι (homogeneous pieces) (linearSection pieces d hd)
      (linearSection_homogeneous pieces d hd) (by decide : 0<1))).inv ≫
        (restrictFunctor (Proj.awayι (homogeneous pieces) (linearSection pieces d hd)
          (linearSection_homogeneous pieces d hd) (by decide : 0<1))).map
            (G c hc) =
      scalar ((Scheme.ΓSpecIso (.of (Away (homogeneous pieces) (linearSection pieces d hd)))).inv
        (Proj.degreeOneFraction (homogeneous pieces) (linearSection_homogeneous pieces d hd)
          (linearSection_homogeneous pieces c hc))) ≫
      (restrictUnitIso (Proj.awayι (homogeneous pieces) (linearSection pieces d hd)
        (linearSection_homogeneous pieces d hd) (by decide : 0<1))).inv ≫
      (restrictFunctor (Proj.awayι (homogeneous pieces) (linearSection pieces d hd)
        (linearSection_homogeneous pieces d hd) (by decide : 0<1))).map
          (G d hd) := by
  exact source_degreeOne_ratio
    (linearSection_homogeneous pieces d hd) (linearSection_homogeneous pieces c hc)
    (G c hc) (G d hd)
    (fun i => G (projectiveParameter i) (projectiveParameter_mem i))
    (fun i => hG i c hc) (fun i => hG i d hd)

lemma degreeOneConormal_projective_ratio (c d : L) (hc : c ∈ pieces 1) (hd : d ∈ pieces 1) :
    (restrictUnitIso (Proj.awayι (homogeneous pieces) (linearSection pieces d hd)
      (linearSection_homogeneous pieces d hd) (by decide : 0<1))).inv ≫
        (restrictFunctor (Proj.awayι (homogeneous pieces) (linearSection pieces d hd)
          (linearSection_homogeneous pieces d hd) (by decide : 0<1))).map
            (degreeOneConormalGenerator c hc) =
      scalar ((Scheme.ΓSpecIso (.of (Away (homogeneous pieces) (linearSection pieces d hd)))).inv
        (Proj.degreeOneFraction (homogeneous pieces) (linearSection_homogeneous pieces d hd)
          (linearSection_homogeneous pieces c hc))) ≫
      (restrictUnitIso (Proj.awayι (homogeneous pieces) (linearSection pieces d hd)
        (linearSection_homogeneous pieces d hd) (by decide : 0<1))).inv ≫
      (restrictFunctor (Proj.awayι (homogeneous pieces) (linearSection pieces d hd)
        (linearSection_homogeneous pieces d hd) (by decide : 0<1))).map
          (degreeOneConormalGenerator d hd) := by
  exact degreeOne_projective_ratio_template degreeOneConormalGenerator
    degreeOneConormalFraction_ratio c d hc hd
end SourcePullbackChart


/-! Conormal frames and transitions on the Kummer coefficient charts. -/
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite _root_.HomogeneousLocalization _root_.OAI.HomogeneousLocalization
namespace ActualSections
open Scheme.Modules
lemma restrict_isIso_comp {X Y Z : Scheme.{0}} (i : X ⟶ Y) (j : Z ⟶ X)
    [IsOpenImmersion i] [IsOpenImmersion j] {M N : Y.Modules} (f : M ⟶ N)
    [IsIso ((restrictFunctor i).map f)] :
    IsIso ((restrictFunctor (j ≫ i)).map f) := by
  have hh : IsIso ((restrictFunctor j).map ((restrictFunctor i).map f)) := inferInstance
  exact (NatIso.isIso_map_iff (restrictFunctorComp j i) f).mpr hh
end ActualSections
namespace SourceSymmetry
open ExplicitCone SourcePullbackChart SourceZeroSections Scheme.Modules ActualCartier ActualSections
abbrev originalConormal : projectiveSurface.Modules :=
  (Scheme.Modules.pullback completedSourceZero).obj (idealSheaf completedSourceZero)

def conormalSection (s : SectionIndex) :
    SheafOfModules.unit projectiveSurface.ringCatSheaf ⟶ originalConormal :=
  degreeOneConormalGenerator (sectionCoefficient s) (sectionCoefficient_mem_piece s)

def conormalChartSection (s t : SectionIndex) (ht : Good t) :
    SheafOfModules.unit (Spec (.of (coefficientChart t))).ringCatSheaf ⟶
      (restrictFunctor (coefficientIota t ht)).obj originalConormal :=
  (restrictUnitIso (coefficientIota t ht)).inv ≫
    (restrictFunctor (coefficientIota t ht)).map (conormalSection s)

lemma conormalChartSection_isIso (t : SectionIndex) (ht : Good t) :
    IsIso (conormalChartSection t t ht) := by
  let : IsIso ((restrictFunctor (Proj.basicOpen grading (projSection t)).ι).map
      (conormalSection t)) :=
    degreeOneConormal_isIso_on (sectionCoefficient t) (sectionCoefficient_mem_piece t)
  let : IsIso ((restrictFunctor (coefficientIota t ht)).map (conormalSection t)) :=
    restrict_isIso_comp (Proj.basicOpen grading (projSection t)).ι
    (projOpenIso t ht).inv (conormalSection t)
  dsimp only [conormalChartSection]
  exact IsIso.comp_isIso'
    (restrictUnitIso (coefficientIota t ht)).isIso_inv
    (inferInstance : IsIso ((restrictFunctor (coefficientIota t ht)).map (conormalSection t)))

lemma projChartEquiv_degreeOneFraction (s t : SectionIndex) (ht : Good t) :
    projChartEquiv t ht (Proj.degreeOneFraction grading (projSection_degree t)
      (projSection_degree s)) = chartRatio t s := by
  simpa only [Proj.degreeOneFraction, Away.isLocalizationElem, pow_one] using
    projChartEquiv_localizationElem t s ht

lemma conormalChartSection_ratio (s t : SectionIndex) (ht : Good t) :
    conormalChartSection s t ht =
      scalar ((Scheme.ΓSpecIso (.of (coefficientChart t))).inv (chartRatio t s)) ≫
        conormalChartSection t t ht := by
  let : IsIso (CommRingCat.ofHom (projChartEquiv t ht).toRingHom) :=
    (projChartEquiv t ht).toRingEquiv.toCommRingCatIso.isIso_hom
  have hr := degreeOneConormal_projective_ratio (sectionCoefficient s) (sectionCoefficient t)
    (sectionCoefficient_mem_piece s) (sectionCoefficient_mem_piece t)
  have hh := restrict_ratio_comp
    (Proj.awayι grading (projSection t) (projSection_degree t) (by decide : 0<1))
    (Spec.map (CommRingCat.ofHom (projChartEquiv t ht).toRingHom))
    (conormalSection s) (conormalSection t) _ hr
  have ha := specMap_inv (projChartEquiv t ht).toRingHom
    (Proj.degreeOneFraction grading (projSection_degree t) (projSection_degree s))
  have ha' := ha.trans (congrArg (Scheme.ΓSpecIso (.of (coefficientChart t))).inv
    (projChartEquiv_degreeOneFraction s t ht))
  exact hh.trans (by
    apply scalar_comp_congr ha')
end SourceSymmetry


/-! Local frames induced by global unit morphisms. -/
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualLineFrames
open Scheme.Modules ActualSections
variable {X Y : Scheme.{0}} (i : X ⟶ Y) [IsOpenImmersion i] {M : Y.Modules}
local instance (U : Y.Opens) : CommRing ((Y.ringCatSheaf.obj).obj (op U)) :=
  inferInstanceAs (CommRing (Y.sheaf.obj.obj (op U)))
local instance (U : X.Opens) : CommRing ((X.ringCatSheaf.obj).obj (op U)) :=
  inferInstanceAs (CommRing (X.sheaf.obj.obj (op U)))

local instance globalRestrictedImageModule (V : X.Opens) :
    Module Γ(Y,i ''ᵁ V) ((M.restrict i).val.obj (op V)) :=
  inferInstanceAs (Module Γ(Y,i ''ᵁ V) (M.val.obj (op (i ''ᵁ V))))

def globalFrame (g : SheafOfModules.unit Y.ringCatSheaf ⟶ M) (U : Y.Opens) : Γ(M,U) :=
  g.val.app (op U) (1 : Γ(Y,U))

lemma globalFrame_restrict (g : SheafOfModules.unit Y.ringCatSheaf ⟶ M)
    {U V : Y.Opens} (h : V ≤ U) :
    M.val.map (homOfLE h).op (globalFrame g U) = globalFrame g V := by
  have he := PresheafOfModules.naturality_apply g.val (homOfLE h).op (1 : Γ(Y,U))
  have hh : (SheafOfModules.unit Y.ringCatSheaf).val.map (homOfLE h).op
      (1 : Γ(Y,U)) = (1 : Γ(Y,V)) := map_one (Y.presheaf.map (homOfLE h).op).hom
  rw [hh] at he
  exact he.symm

lemma restricted_globalFrame (g : SheafOfModules.unit Y.ringCatSheaf ⟶ M) :
    ((restrictUnitIso i).inv ≫ (restrictFunctor i).map g).val.app (op ⊤)
      (1 : Γ(X,⊤)) = globalFrame g (i ''ᵁ ⊤) := by
  change g.val.app (op (i ''ᵁ ⊤)) ((i.appIso ⊤).inv (1 : Γ(X,⊤))) = _
  rw [map_one]
  rfl

lemma globalFrame_isIso (g : SheafOfModules.unit Y.ringCatSheaf ⟶ M)
    [IsIso ((restrictUnitIso i).inv ≫ (restrictFunctor i).map g)] :
    IsIso (overFromSection M (i ''ᵁ ⊤) (globalFrame g (i ''ᵁ ⊤))) := by
  let e := (asIso ((restrictUnitIso i).inv ≫ (restrictFunctor i).map g)).symm
  have he : chartFrame i e = globalFrame g (i ''ᵁ ⊤) := restricted_globalFrame i g
  rw [← he]
  exact chartFrame_isIso i e

lemma globalFrame_ratio (s t : SheafOfModules.unit Y.ringCatSheaf ⟶ M)
    (a : Γ(X,⊤))
    (hr : (restrictUnitIso i).inv ≫ (restrictFunctor i).map s =
      scalar a ≫ (restrictUnitIso i).inv ≫ (restrictFunctor i).map t) :
    globalFrame s (i ''ᵁ ⊤) = (i.appIso ⊤).inv a • globalFrame t (i ''ᵁ ⊤) := by
  have hh := congrArg (fun f : SheafOfModules.unit X.ringCatSheaf ⟶ M.restrict i =>
    f.val.app (op ⊤) (1 : Γ(X,⊤))) hr
  rw [restricted_globalFrame] at hh
  change globalFrame s (i ''ᵁ ⊤) =
    ((restrictUnitIso i).inv ≫ (restrictFunctor i).map t).val.app (op ⊤)
      ((scalar a).val.app (op ⊤) (1 : Γ(X,⊤))) at hh
  erw [fromUnit_top, one_smul] at hh
  have hl := (((restrictUnitIso i).inv ≫ (restrictFunctor i).map t).val.app
    (op ⊤)).hom.map_smul a (1 : Γ(X,⊤))
  change ((restrictUnitIso i).inv ≫ (restrictFunctor i).map t).val.app (op ⊤)
      (a * (1 : Γ(X,⊤))) =
    (i.appIso ⊤).inv a •
      (((restrictUnitIso i).inv ≫ (restrictFunctor i).map t).val.app (op ⊤)
        (1 : Γ(X,⊤)) : Γ(M,i ''ᵁ ⊤)) at hl
  rw [mul_one, restricted_globalFrame] at hl
  exact hh.trans hl
end ActualLineFrames


/-! A global unit morphism gives a unit isomorphism on its invertibility locus. -/
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualLineFrames
open Scheme.Modules
variable {X Y : Scheme.{0}} (i : X ⟶ Y) [IsOpenImmersion i] {M : Y.Modules}
local instance (U : Y.Opens) : CommRing ((Y.ringCatSheaf.obj).obj (op U)) :=
  inferInstanceAs (CommRing (Y.sheaf.obj.obj (op U)))

def globalOpenUnitIso (g : SheafOfModules.unit Y.ringCatSheaf ⟶ M)
    [IsIso ((restrictUnitIso i).inv ≫ (restrictFunctor i).map g)] :
    M.over (i ''ᵁ ⊤) ≅ SheafOfModules.unit (Y.ringCatSheaf.over (i ''ᵁ ⊤)) :=
  letI := globalFrame_isIso i g
  (asIso (overFromSection M (i ''ᵁ ⊤) (globalFrame g (i ''ᵁ ⊤)))).symm

lemma globalOpenUnitIso_frame (g : SheafOfModules.unit Y.ringCatSheaf ⟶ M)
    [IsIso ((restrictUnitIso i).inv ≫ (restrictFunctor i).map g)]
    (V : Y.Opens) (h : V ≤ i ''ᵁ ⊤) :
    frame (globalOpenUnitIso i g) V h = globalFrame g V := by
  let := globalFrame_isIso i g
  exact (overFromSection_frame (globalFrame g (i ''ᵁ ⊤)) V h).trans
    (globalFrame_restrict g h)

lemma globalFrame_ratio_restrict (s t : SheafOfModules.unit Y.ringCatSheaf ⟶ M)
    (U V : Y.Opens) (h : V ≤ U) (a : Γ(Y,U))
    (hr : globalFrame s U = a • globalFrame t U) :
    globalFrame s V = Y.presheaf.map (homOfLE h).op a • globalFrame t V := by
  have hh := congrArg (M.val.map (homOfLE h).op) hr
  erw [_root_.map_smul, globalFrame_restrict, globalFrame_restrict] at hh
  exact hh
end ActualLineFrames


/-! Conormal frames and transitions on the canonical-sheaf chart cover. -/
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace SourceSymmetry
open ExplicitCone ActualLineFrames
local instance (U : projectiveSurface.Opens) : CommRing
    ((projectiveSurface.ringCatSheaf.obj).obj (op U)) :=
  inferInstanceAs (CommRing (projectiveSurface.sheaf.obj.obj (op U)))
local instance (R : Type) [CommRing R] (U : (Spec (.of R)).Opens) :
    Algebra R Γ(Spec (.of R),U) :=
  inferInstanceAs (Algebra R ((Spec.structureSheaf R).obj.obj (op U)))

def conormalOpenUnitIso (t : SectionIndex) (ht : Good t) :
    originalConormal.over (coefficientIota t ht ''ᵁ ⊤) ≅
      SheafOfModules.unit (projectiveSurface.ringCatSheaf.over (coefficientIota t ht ''ᵁ ⊤)) := by
  haveI : IsIso ((Scheme.Modules.restrictUnitIso (coefficientIota t ht)).inv ≫
      (Scheme.Modules.restrictFunctor (coefficientIota t ht)).map (conormalSection t)) :=
    conormalChartSection_isIso t ht
  exact globalOpenUnitIso (coefficientIota t ht) (conormalSection t)

lemma conormalOpenUnitIso_frame (t : SectionIndex) (ht : Good t)
    (V : projectiveSurface.Opens) (h : V ≤ coefficientIota t ht ''ᵁ ⊤) :
    frame (conormalOpenUnitIso t ht) V h = globalFrame (conormalSection t) V := by
  have : IsIso ((Scheme.Modules.restrictUnitIso (coefficientIota t ht)).inv ≫
      (Scheme.Modules.restrictFunctor (coefficientIota t ht)).map (conormalSection t)) :=
    conormalChartSection_isIso t ht
  exact globalOpenUnitIso_frame (coefficientIota t ht) (conormalSection t) V h

lemma conormalFrame_ratio (s t : SectionIndex) (ht : Good t) :
    globalFrame (conormalSection s) (coefficientIota t ht ''ᵁ ⊤) =
      ActualCotangent.chartCoordinate (coefficientChart t) (coefficientIota t ht) (chartRatio t s) •
        globalFrame (conormalSection t) (coefficientIota t ht ''ᵁ ⊤) := by
  exact globalFrame_ratio (coefficientIota t ht) (conormalSection s) (conormalSection t)
    ((Scheme.ΓSpecIso (.of (coefficientChart t))).inv (chartRatio t s))
    (conormalChartSection_ratio s t ht)

/-- The linear transition, in the common-open ring. -/
def conormalOverlapRatio (s t : SectionIndex) : coefficientOverlap s t :=
  Subalgebra.inclusion (coefficientChart_le_overlap_right s t) (chartRatio t s)

lemma canonicalOverlapRatio_is_power (s t : SectionIndex) :
    canonicalOverlapRatio s t = (conormalOverlapRatio s t)^5 := by
  rfl

lemma intrinsic_conormal_transition (s t : SectionIndex) (hs : Good s) (ht : Good t) :
    globalFrame (conormalSection s) (coefficientOverlapIota s t hs ''ᵁ ⊤) =
      ActualCotangent.chartCoordinate (coefficientOverlap s t) (coefficientOverlapIota s t hs)
        (conormalOverlapRatio s t) •
      globalFrame (conormalSection t) (coefficientOverlapIota s t hs ''ᵁ ⊤) := by
  let := Subalgebra.inclusionAlgebra (coefficientChart t) (coefficientOverlap s t)
    (coefficientChart_le_overlap_right s t)
  have h := globalFrame_ratio_restrict (conormalSection s) (conormalSection t)
    (coefficientIota t ht ''ᵁ ⊤) (coefficientOverlapIota s t hs ''ᵁ ⊤)
    (coefficientOverlap_le_right s t hs ht) _ (conormalFrame_ratio s t ht)
  have hr := ActualCotangent.chartCoordinate_restrict
    (coefficientIota t ht) (coefficientOverlapIota s t hs)
    (coefficientOverlapIota_right s t hs ht) (coefficientOverlap_le_right s t hs ht)
    (chartRatio t s)
  exact h.trans (congrArg (fun a => a • globalFrame (conormalSection t)
    (coefficientOverlapIota s t hs ''ᵁ ⊤)) hr)
end SourceSymmetry


/-! Tensor powers of line sheaves and their sections. -/
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
open scoped TensorProduct
namespace ActualSheafTensor
universe u
variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

def tensorPower (M : SheafOfModules.{u} (ringSheaf R)) : ℕ → SheafOfModules.{u} (ringSheaf R)
  | 0 => SheafOfModules.unit (ringSheaf R)
  | n+1 => tensor R M (tensorPower M n)

def powerSection (M : SheafOfModules.{u} (ringSheaf R)) (U : Cᵒᵖ) (s : M.val.obj U) :
    (n : ℕ) → (tensorPower R M n).val.obj U
  | 0 => (1 : R.obj.obj U)
  | n+1 => pure R M (tensorPower R M n) U s (powerSection M U s n)

lemma pure_smul_left (M N : SheafOfModules.{u} (ringSheaf R)) (U : Cᵒᵖ) (a : R.obj.obj U)
    (s : M.val.obj U) (t : N.val.obj U) :
    pure R M N U (a • s) t = a • pure R M N U s t := by
  unfold pure
  rw [← TensorProduct.smul_tmul']
  erw [map_smul]
  rfl

lemma pure_smul_right (M N : SheafOfModules.{u} (ringSheaf R)) (U : Cᵒᵖ) (a : R.obj.obj U)
    (s : M.val.obj U) (t : N.val.obj U) :
    pure R M N U s (a • t) = a • pure R M N U s t := by
  unfold pure
  rw [TensorProduct.tmul_smul]
  erw [map_smul]
  rfl

lemma powerSection_smul (M : SheafOfModules.{u} (ringSheaf R)) (U : Cᵒᵖ) (a : R.obj.obj U)
    (s : M.val.obj U) (n : ℕ) :
    powerSection R M U (a • s) n = a^n • powerSection R M U s n := by
  induction n with
  | zero =>
    simp only [powerSection, pow_zero]
    change (1 : R.obj.obj U) = (1 : R.obj.obj U) * 1
    exact (one_mul _).symm
  | succ n ih =>
    change pure _ _ _ _ (a • s) (powerSection R M U (a • s) n) = _
    rw [ih, pure_smul_left, pure_smul_right, smul_smul, ← pow_succ']
    rfl

lemma powerSection_restrict (M : SheafOfModules.{u} (ringSheaf R)) (U V : Cᵒᵖ) (h : U ⟶ V)
    (s : M.val.obj U) (n : ℕ) :
    (tensorPower R M n).val.map h (powerSection R M U s n) =
      powerSection R M V (M.val.map h s) n := by
  induction n with
  | zero => exact map_one (R.obj.map h).hom
  | succ n ih =>
    change (tensor _ _ _).val.map _ (pure _ _ _ _ _ _) = _
    rw [pure_naturality, ih]
    rfl
end ActualSheafTensor


/-! Local frames for tensor powers of line sheaves. -/
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
open scoped TensorProduct
namespace ActualSheafTensor
universe u
variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

def powerUnitIso {M : SheafOfModules (ringSheaf R)}
    (e : M ≅ SheafOfModules.unit (ringSheaf R)) :
    (n : ℕ) → tensorPower R M n ≅ SheafOfModules.unit (ringSheaf R)
  | 0 => Iso.refl _
  | n+1 => (trivialTensorIso R e).app (tensorPower R M n) ≪≫ powerUnitIso e n

lemma powerUnitIso_hom_section {M : SheafOfModules (ringSheaf R)}
    (e : M ≅ SheafOfModules.unit (ringSheaf R)) (U : Cᵒᵖ) (n : ℕ) :
    (powerUnitIso R e n).hom.val.app U
      (powerSection R M U (e.inv.val.app U (1 : R.obj.obj U)) n) = (1 : R.obj.obj U) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (powerUnitIso R e n).hom.val.app U
      (((trivialTensorIso R e).hom.app (tensorPower R M n)).val.app U
        (pure R M (tensorPower R M n) U _ _)) = _
    rw [trivialTensorIso_pure]
    have he : e.hom.val.app U (e.inv.val.app U (1 : R.obj.obj U)) = (1 : R.obj.obj U) :=
      congrArg (fun f : SheafOfModules.unit (ringSheaf R) ⟶ SheafOfModules.unit (ringSheaf R) =>
        f.val.app U (1 : R.obj.obj U)) e.inv_hom_id
    erw [he, one_smul]
    exact ih

lemma powerUnitIso_inv_one {M : SheafOfModules (ringSheaf R)}
    (e : M ≅ SheafOfModules.unit (ringSheaf R)) (U : Cᵒᵖ) (n : ℕ) :
    (powerUnitIso R e n).inv.val.app U (1 : R.obj.obj U) =
      powerSection R M U (e.inv.val.app U (1 : R.obj.obj U)) n := by
  have h := powerUnitIso_hom_section R e U n
  have hi := congrArg ((powerUnitIso R e n).inv.val.app U) h
  have hc : (powerUnitIso R e n).inv.val.app U
      ((powerUnitIso R e n).hom.val.app U
        (powerSection R M U (e.inv.val.app U (1 : R.obj.obj U)) n)) =
      powerSection R M U (e.inv.val.app U (1 : R.obj.obj U)) n :=
    ConcreteCategory.congr_hom
      (congrArg (fun f => f.val.app U) (powerUnitIso R e n).hom_inv_id) _
  exact hi.symm.trans hc

def tensorRightIso (M : SheafOfModules (ringSheaf R))
    {N P : SheafOfModules (ringSheaf R)} (e : N ≅ P) :
    tensor R M N ≅ tensor R M P := (tensorLeft R M).mapIso e

lemma tensorRightIso_inv_pure (M : SheafOfModules (ringSheaf R))
    {N P : SheafOfModules (ringSheaf R)} (e : N ≅ P)
    (V : Cᵒᵖ) (s : M.val.obj V) (t : P.val.obj V) :
    (tensorRightIso R M e).inv.val.app V (pure R M P V s t) =
      pure R M N V s (e.inv.val.app V t) := tensorLeft_map_pure R M e.inv V s t

variable (U : C)
  [HasSheafify (J.over U) AddCommGrpCat.{u}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

def powerOverIso (M : SheafOfModules (ringSheaf R)) :
    (n : ℕ) → (tensorPower R M n).over U ≅ tensorPower (R.over U) (M.over U) n
  | 0 => Iso.refl _
  | n+1 => tensorOverIso R U M (tensorPower R M n) ≪≫
      tensorRightIso (R.over U) (M.over U) (powerOverIso M n)

lemma tensorOverIso_inv_pure (M N : SheafOfModules (ringSheaf R))
    (V : (Over U)ᵒᵖ) (s : (M.over U).val.obj V) (t : (N.over U).val.obj V) :
    (tensorOverIso R U M N).inv.val.app V
      (pure (R.over U) (M.over U) (N.over U) V s t) =
      pure R M N (op V.unop.left) s t := by
  have h := tensorOverIso_inv_adjoint R U M N
  erw [Adjunction.homEquiv_unit] at h
  exact congrArg (fun f => f.app V (s ⊗ₜ[(R.over U).obj.obj V] t)) h

lemma powerOverIso_step (M : SheafOfModules (ringSheaf R))
    (V : (Over U)ᵒᵖ) (s : (M.over U).val.obj V) (n : ℕ)
    (ih : (powerOverIso R U M n).inv.val.app V
      (powerSection (R.over U) (M.over U) V s n) =
      powerSection R M (op V.unop.left) s n) :
    (powerOverIso R U M (n+1)).inv.val.app V
      (pure (R.over U) (M.over U) (tensorPower (R.over U) (M.over U) n) V s
        (powerSection (R.over U) (M.over U) V s n)) =
      pure R M (tensorPower R M n) (op V.unop.left) s
        (powerSection R M (op V.unop.left) s n) := by
  have hcomp : (powerOverIso R U M (n+1)).inv =
      (tensorRightIso (R.over U) (M.over U) (powerOverIso R U M n)).inv ≫
        (tensorOverIso R U M (tensorPower R M n)).inv := rfl
  have hh := congrArg (fun f => f.val.app V
    (pure (R.over U) (M.over U) (tensorPower (R.over U) (M.over U) n) V s
      (powerSection (R.over U) (M.over U) V s n))) hcomp
  refine hh.trans ?_
  change (tensorOverIso R U M (tensorPower R M n)).inv.val.app V
    ((tensorRightIso (R.over U) (M.over U) (powerOverIso R U M n)).inv.val.app V
      (pure (R.over U) (M.over U) (tensorPower (R.over U) (M.over U) n) V s
        (powerSection (R.over U) (M.over U) V s n))) = _
  have hright := tensorRightIso_inv_pure (R.over U) (M.over U)
    (powerOverIso R U M n) V s (powerSection (R.over U) (M.over U) V s n)
  have hleft := tensorOverIso_inv_pure R U M (tensorPower R M n) V s
    ((powerOverIso R U M n).inv.val.app V (powerSection (R.over U) (M.over U) V s n))
  exact (congrArg (fun z => (tensorOverIso R U M (tensorPower R M n)).inv.val.app V z)
    hright).trans (hleft.trans
      (congrArg (pure R M (tensorPower R M n) (op V.unop.left) s) ih))

lemma powerOverIso_inv_section (M : SheafOfModules (ringSheaf R))
    (V : (Over U)ᵒᵖ) (s : (M.over U).val.obj V) (n : ℕ) :
    (powerOverIso R U M n).inv.val.app V
      (powerSection (R.over U) (M.over U) V s n) =
      powerSection R M (op V.unop.left) s n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa only [powerSection] using powerOverIso_step R U M V s n ih
end ActualSheafTensor


/-! Tensor-power frames on scheme open sets. -/
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualLineFrames
open ActualSheafTensor
variable {X : Scheme.{0}}
local instance powerFrameGluingOpenCommRing (U : X.Opens) : CommRing ((X.ringCatSheaf.obj).obj (op U)) :=
  inferInstanceAs (CommRing (X.sheaf.obj.obj (op U)))

def overPowerFrameIso {M : X.Modules} {U : X.Opens}
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) (n : ℕ) :
    (tensorPower X.sheaf M n).over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U) :=
  powerOverIso X.sheaf U M n ≪≫ powerUnitIso (X.sheaf.over U) e n

lemma overPowerFrameIso_frame {M : X.Modules} {U : X.Opens}
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (V : X.Opens) (h : V ≤ U) (n : ℕ) :
    frame (overPowerFrameIso e n) V h = powerSection X.sheaf M (op V) (frame e V h) n := by
  change (powerOverIso X.sheaf U M n).inv.val.app (op (Over.mk (homOfLE h)))
    ((powerUnitIso (X.sheaf.over U) e n).inv.val.app (op (Over.mk (homOfLE h)))
      (1 : Γ(X,V))) = _
  erw [powerUnitIso_inv_one]
  exact powerOverIso_inv_section X.sheaf U M (op (Over.mk (homOfLE h))) _ n

lemma powerFrame_matching {M : X.Modules} (U W V : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (f : M.over W ≅ SheafOfModules.unit (X.ringCatSheaf.over W))
    (hU : V ≤ U) (hW : V ≤ W) (a : Γ(X,V))
    (he : frame e V hU = a • frame f V hW) (n : ℕ) :
    frame (overPowerFrameIso e n) V hU = a^n • frame (overPowerFrameIso f n) V hW := by
  rw [overPowerFrameIso_frame, overPowerFrameIso_frame, he]
  exact powerSection_smul X.sheaf M (op V) a (frame f V hW) n
end ActualLineFrames


/-! Restriction of section transition equations. -/
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualLineFrames
variable {X : Scheme.{0}}
local instance sectionTransitionOpenCommRing (U : X.Opens) : CommRing ((X.ringCatSheaf.obj).obj (op U)) :=
  inferInstanceAs (CommRing (X.sheaf.obj.obj (op U)))
lemma section_transition_restrict (M : X.Modules) {U W Z V : X.Opens}
    (hZU : Z ≤ U) (hZW : Z ≤ W) (hVZ : V ≤ Z)
    (s : Γ(M,U)) (t : Γ(M,W)) (a : Γ(X,Z))
    (he : M.val.map (homOfLE hZU).op s = a • M.val.map (homOfLE hZW).op t) :
    M.val.map (homOfLE (hVZ.trans hZU)).op s =
      X.presheaf.map (homOfLE hVZ).op a •
        M.val.map (homOfLE (hVZ.trans hZW)).op t := by
  have hh := congrArg (M.val.map (homOfLE hVZ).op) he
  erw [map_smul, ← PresheafOfModules.map_comp_apply, ← PresheafOfModules.map_comp_apply] at hh
  exact hh
lemma section_transition_power_restrict (M : X.Modules) {U W Z V : X.Opens}
    (hZU : Z ≤ U) (hZW : Z ≤ W) (hVZ : V ≤ Z)
    (s : Γ(M,U)) (t : Γ(M,W)) (a : Γ(X,Z)) (n : ℕ)
    (he : M.val.map (homOfLE hZU).op s = a^n • M.val.map (homOfLE hZW).op t) :
    M.val.map (homOfLE (hVZ.trans hZU)).op s =
      (X.presheaf.map (homOfLE hVZ).op a)^n •
        M.val.map (homOfLE (hVZ.trans hZW)).op t := by
  have hh := section_transition_restrict M hZU hZW hVZ s t (a^n) he
  rw [map_pow] at hh
  exact hh
end ActualLineFrames


/-! Restriction of section power transitions to line frames. -/
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualLineFrames
variable {X : Scheme.{0}}
local instance sectionPowerFramesOpenCommRing (U : X.Opens) :
    CommRing ((X.ringCatSheaf.obj).obj (op U)) :=
  inferInstanceAs (CommRing (X.sheaf.obj.obj (op U)))
lemma section_power_frame_restrict (M : X.Modules) {U W Z V : X.Opens}
    (hZU : Z ≤ U) (hZW : Z ≤ W) (hVZ : V ≤ Z)
    (hVU : V ≤ U) (hVW : V ≤ W)
    (s : Γ(M,U)) (t : Γ(M,W)) (a : Γ(X,Z)) (n : ℕ)
    [IsIso (overFromSection M U s)] [IsIso (overFromSection M W t)]
    (he : M.val.map (homOfLE hZU).op s = a^n • M.val.map (homOfLE hZW).op t) :
    frame (asIso (overFromSection M U s)).symm V hVU =
      (X.presheaf.map (homOfLE hVZ).op a)^n •
        frame (asIso (overFromSection M W t)).symm V hVW := by
  rw [overFromSection_frame, overFromSection_frame]
  exact section_transition_power_restrict M hZU hZW hVZ s t a n he
lemma section_scalar_power_frame_restrict (M : X.Modules) {U W Z V : X.Opens}
    (hZU : Z ≤ U) (hZW : Z ≤ W) (hVZ : V ≤ Z)
    (hVU : V ≤ U) (hVW : V ≤ W)
    (s : Γ(M,U)) (t : Γ(M,W)) {A : Type} [CommRing A]
    (f : A →+* Γ(X,Z)) (a : A) (n : ℕ)
    [IsIso (overFromSection M U s)] [IsIso (overFromSection M W t)]
    (he : M.val.map (homOfLE hZU).op s =
      ActualSections.scalarMul M Z (f (a^n)) (M.val.map (homOfLE hZW).op t)) :
    frame (asIso (overFromSection M U s)).symm V hVU =
      (X.presheaf.map (homOfLE hVZ).op (f a))^n •
        frame (asIso (overFromSection M W t)).symm V hVW := by
  apply section_power_frame_restrict M hZU hZW hVZ hVU hVW s t (f a) n
  have he' : M.val.map (homOfLE hZU).op s =
      (f (a^n)) • M.val.map (homOfLE hZW).op t := he
  erw [map_pow] at he'
  exact he'
end ActualLineFrames



/-! The canonical line is the fifth tensor power of the exceptional conormal line. -/
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace SourceSymmetry
open ExplicitCone ActualLineFrames ActualSheafTensor
local instance (U : projectiveSurface.Opens) : CommRing
    ((projectiveSurface.ringCatSheaf.obj).obj (op U)) :=
  inferInstanceAs (CommRing (projectiveSurface.sheaf.obj.obj (op U)))

lemma coefficientOverlap_image (s t : SectionIndex) (hs : Good s) (ht : Good t) :
    coefficientOverlapIota s t hs ''ᵁ ⊤ =
      (coefficientIota s hs ''ᵁ ⊤) ⊓ (coefficientIota t ht ''ᵁ ⊤) := by
  simp only [Scheme.Hom.image_top_eq_opensRange, coefficientOverlapIota_opensRange,
    coefficientIota_opensRange]
  rfl

def overlapScalar (s t : SectionIndex) (hs : Good s) :
    Γ(projectiveSurface,coefficientOverlapIota s t hs ''ᵁ ⊤) :=
  ActualCotangent.chartCoordinate (coefficientOverlap s t) (coefficientOverlapIota s t hs)
    (conormalOverlapRatio s t)

lemma canonical_frame_power_transition (s t : SectionIndex) (hs : Good s) (ht : Good t)
    (V : projectiveSurface.Opens) (hVs : V ≤ coefficientIota s hs ''ᵁ ⊤)
    (hVt : V ≤ coefficientIota t ht ''ᵁ ⊤)
    (hV : V ≤ coefficientOverlapIota s t hs ''ᵁ ⊤) :
    frame (canonicalOpenUnitIso s hs) V hVs =
      (projectiveSurface.presheaf.map (homOfLE hV).op (overlapScalar s t hs))^5 •
        frame (canonicalOpenUnitIso t ht) V hVt := by
  exact section_scalar_power_frame_restrict canonicalSheaf
    (coefficientOverlap_le_left s t hs) (coefficientOverlap_le_right s t hs ht)
    hV hVs hVt (canonicalFrameSection s hs) (canonicalFrameSection t ht)
    (ActualCotangent.chartCoordinate (coefficientOverlap s t) (coefficientOverlapIota s t hs))
    (conormalOverlapRatio s t) 5 (intrinsic_canonical_transition s t hs ht)

lemma conormal_frame_linear_transition (s t : SectionIndex) (hs : Good s) (ht : Good t)
    (V : projectiveSurface.Opens) (hVs : V ≤ coefficientIota s hs ''ᵁ ⊤)
    (hVt : V ≤ coefficientIota t ht ''ᵁ ⊤)
    (hV : V ≤ coefficientOverlapIota s t hs ''ᵁ ⊤) :
    frame (conormalOpenUnitIso s hs) V hVs =
      projectiveSurface.presheaf.map (homOfLE hV).op (overlapScalar s t hs) •
        frame (conormalOpenUnitIso t ht) V hVt := by
  have hR := globalFrame_ratio_restrict (conormalSection s) (conormalSection t)
    (coefficientOverlapIota s t hs ''ᵁ ⊤) V hV (overlapScalar s t hs)
    (intrinsic_conormal_transition s t hs ht)
  exact (conormalOpenUnitIso_frame s hs V hVs).trans
    (hR.trans (congrArg
      (fun z => projectiveSurface.presheaf.map (homOfLE hV).op (overlapScalar s t hs) • z)
      (conormalOpenUnitIso_frame t ht V hVt).symm))

lemma canonical_conormal_matching_frames (s t : SectionIndex) (hs : Good s) (ht : Good t)
    (V : projectiveSurface.Opens) (hVs : V ≤ coefficientIota s hs ''ᵁ ⊤)
    (hVt : V ≤ coefficientIota t ht ''ᵁ ⊤) :
    ∃ a : Γ(projectiveSurface,V),
      frame (canonicalOpenUnitIso s hs) V hVs =
        a • frame (canonicalOpenUnitIso t ht) V hVt ∧
      frame (overPowerFrameIso (conormalOpenUnitIso s hs) 5) V hVs =
        a • frame (overPowerFrameIso (conormalOpenUnitIso t ht) 5) V hVt := by
  have hV : V ≤ coefficientOverlapIota s t hs ''ᵁ ⊤ := by
    rw [coefficientOverlap_image s t hs ht]
    exact le_inf hVs hVt
  let a := projectiveSurface.presheaf.map (homOfLE hV).op (overlapScalar s t hs)
  refine ⟨a^5, canonical_frame_power_transition s t hs ht V hVs hVt hV, ?_⟩
  exact powerFrame_matching _ _ V (conormalOpenUnitIso s hs) (conormalOpenUnitIso t ht)
    hVs hVt a (conormal_frame_linear_transition s t hs ht V hVs hVt hV) 5

/-- The canonical/polarization identification on the surface. -/
lemma canonical_originalConormal_pow5 :
    Nonempty (canonicalSheaf ≅ tensorPower projectiveSurface.sheaf originalConormal 5) := by
  exact exists_iso_of_matching_frames canonicalSheaf
    (tensorPower projectiveSurface.sheaf originalConormal 5)
    (fun t : {t : SectionIndex // Good t} => coefficientIota t.val t.property ''ᵁ ⊤)
    (by simpa only [Scheme.Hom.image_top_eq_opensRange] using coefficientIota_cover)
    (fun t => canonicalOpenUnitIso t.val t.property)
    (fun t => overPowerFrameIso (conormalOpenUnitIso t.val t.property) 5)
    (fun s t V hs ht => canonical_conormal_matching_frames s.val t.val s.property t.property V hs ht)
end SourceSymmetry


/-! Regularity of the local rings on the exceptional surface. -/
namespace SourceSymmetry
open ExplicitCone _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry CategoryTheory

lemma coefficientChart_regular (t : SectionIndex) (ht : Good t) :
    IsRegularRing (coefficientChart t) := by
  let := sectionChart_regular
  exact IsRegularRing.of_ringEquiv (goodChartEquiv t ht).toRingEquiv

lemma projChart_regular (t : SectionIndex) (ht : Good t) :
    IsRegularRing (projChart t) := by
  let := coefficientChart_regular t ht
  exact IsRegularRing.of_ringEquiv (projChartEquiv t ht).symm.toRingEquiv

lemma regularStalk_spec {R : Type*} [CommRing R] [IsRegularRing R]
    (x : Spec (.of R)) : IsRegularLocalRing ((Spec (.of R)).presheaf.stalk x) := by
  let := x.isPrime
  exact IsRegularLocalRing.of_ringEquiv (Spec.stalkIso (.of R) x).symm.commRingCatIsoToRingEquiv

lemma regularStalk_open {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f]
    (x : X) [IsRegularLocalRing (X.presheaf.stalk x)] :
    IsRegularLocalRing (Y.presheaf.stalk (f x)) :=
  IsRegularLocalRing.of_ringEquiv (asIso (f.stalkMap x)).symm.commRingCatIsoToRingEquiv

/-- Regularity at EVERY point of the normalized source surface. -/
theorem projectiveSurface_regular (x : projectiveSurface) :
    IsRegularLocalRing (projectiveSurface.presheaf.stalk x) := by
  have hx : x ∈ iSup smoothOpen := by rw [smoothOpen_cover]; trivial
  obtain ⟨t,ht⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  let f := Proj.awayι grading (projSection t.val)
    (SectionCompletion.linearSection_homogeneous pieces _ _) zero_lt_one
  have hf : x ∈ f.opensRange := by
    change x ∈ Proj.basicOpen grading (projSection t.val) at ht
    simpa only [f, Proj.opensRange_awayι] using ht
  obtain ⟨y,hy⟩ := Scheme.Hom.mem_opensRange.mp hf
  let := projChart_regular t.val t.property
  let := regularStalk_spec (R := projChart t.val) y
  rw [← hy]
  exact regularStalk_open f y

end SourceSymmetry


/-! The normalized projective surface has dimension two. -/
universe u v
namespace SourceSymmetry
open ExplicitCone _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry CategoryTheory TopologicalSpace Order

attribute [local instance] specializationOrder in
lemma dimension_le_of_open_cover {X : Type u} [TopologicalSpace X] [QuasiSober X] [T0Space X]
    {ι : Type v} (U : ι → TopologicalSpace.Opens X) (hU : iSup U = ⊤)
    (n : WithBot ℕ∞) (h : ∀ i, topologicalKrullDim (U i) ≤ n) :
    topologicalKrullDim X ≤ n := by
  have hd (Y : Type u) [TopologicalSpace Y] [QuasiSober Y] [T0Space Y] :
      topologicalKrullDim Y = Order.krullDim Y :=
    Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := Y))
  rw [hd X, Order.krullDim_eq_iSup_coheight]
  apply iSup_le
  intro x
  have hx : x ∈ iSup U := by rw [hU]; trivial
  obtain ⟨i,hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  let := (U i).isOpenEmbedding'.quasiSober
  let : PartialOrder (U i) := specializationOrder (U i)
  have he := (U i).isOpenEmbedding'.coheight_eq (f := fun y : U i => (y : X))
    (x := ⟨x,hi⟩)
  rw [he]
  exact (@Order.coheight_le_krullDim (U i) (specializationOrder (U i)).toPreorder
    ⟨x,hi⟩).trans ((hd (U i)) ▸ h i)

lemma projChart_dimension (t : SectionIndex) (ht : Good t) :
    ringKrullDim (projChart t) = 2 := by
  calc
    ringKrullDim (projChart t) = ringKrullDim (coefficientChart t) :=
      (projChartEquiv t ht).toRingEquiv.ringKrullDim
    _ = ringKrullDim sectionChart := (goodChartEquiv t ht).symm.toRingEquiv.ringKrullDim
    _ = 2 := sectionChart_dimension

lemma smoothOpen_dimension (t : GoodIndex) :
    topologicalKrullDim (smoothOpen t) = 2 := by
  let e := Proj.basicOpenIsoSpec grading (projSection t.val)
    (SectionCompletion.linearSection_homogeneous pieces _ _) zero_lt_one
  calc
    topologicalKrullDim (smoothOpen t) = topologicalKrullDim (Spec (.of (projChart t.val))) :=
      IsHomeomorph.topologicalKrullDim_eq _ e.hom.homeomorph.isHomeomorph
    _ = ringKrullDim (projChart t.val) := PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _
    _ = 2 := projChart_dimension t.val t.property

/-- The source Proj is a surface. -/
theorem projectiveSurface_dimension : topologicalKrullDim projectiveSurface = 2 := by
  apply le_antisymm
  · exact dimension_le_of_open_cover smoothOpen smoothOpen_cover _
      (fun i => (smoothOpen_dimension i).le)
  · let t : GoodIndex := ⟨(0,0), by unfold Good; decide⟩
    rw [← smoothOpen_dimension t]
    exact topologicalKrullDim_subspace_le projectiveSurface (smoothOpen t)

end SourceSymmetry

end

end OAI
