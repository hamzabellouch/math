import OAI.AlgebraicGeometry.SurfaceCones.AffineExteriorSections
import OAI.AlgebraicGeometry.SurfaceCones.ScalarPullback

namespace OAI

private local instance frameFiniteQuasicoherent {Z : AlgebraicGeometry.Scheme.{0}}
    (M : Z.Modules) [M.IsFinitePresentation] : M.IsQuasicoherent :=
  (SheafOfModules.IsFinitePresentation.exists_quasicoherentData M).choose.isQuasicoherent

/-! An affine module basis induces a line frame in its associated sheaf. -/
noncomputable section
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualLineFrames
variable {Y : Scheme.{0}} (R : Type) [CommRing R]
  (i : Spec (.of R) ⟶ Y) [IsOpenImmersion i]
  (M : Y.Modules) (N : ModuleCat R) (e : M.restrict i ≅ tilde N)
  (b : N ≅ ModuleCat.of R R)

local instance (U : (Spec (.of R)).Opens) : Algebra R Γ(Spec (.of R),U) :=
  inferInstanceAs (Algebra R ((Spec.structureSheaf R).obj.obj (.op U)))

lemma tildeSelf_inv_one : (tildeSelf (R := .of R)).inv.val.app (op ⊤)
    (1 : Γ(Spec (.of R),⊤)) = tilde.toOpen (R := .of R) (ModuleCat.of R R) ⊤ 1 := by
  change (1 : Γ(Spec (.of R),⊤)) = algebraMap R Γ(Spec (.of R),⊤) 1
  exact (map_one _).symm

lemma affineUnit_chartFrame :
    chartFrame i (e ≪≫ (tilde.functor (.of R)).mapIso b ≪≫ tildeSelf) =
      ActualSections.affineSection R i M N e (b.inv 1) := by
  unfold chartFrame ActualSections.affineSection
  change e.inv.val.app (op ⊤)
    ((tilde.map b.inv).val.app (op ⊤)
      ((tildeSelf (R := .of R)).inv.val.app (op ⊤) (1 : Γ(Spec (.of R),⊤)))) = _
  rw [tildeSelf_inv_one]
  exact congrArg (e.inv.val.app (op ⊤))
    (ConcreteCategory.congr_hom (tilde.toOpen_map_app (R := .of R) b.inv ⊤) 1)
end ActualLineFrames

end

/-! The canonical top-form sections are frames on the coefficient-chart cover. -/
noncomputable section
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace SourceSymmetry
open ExplicitCone ActualLineFrames
lemma coefficientCanonicalIso_eq_top (t : SectionIndex) (ht : Good t) :
    coefficientCanonicalIso t ht =
      ActualCotangent.topOpenAffineIso projectiveSurfaceToComplex (coefficientChart t)
        (coefficientIota t ht) (coefficientIota_toComplex t ht) := rfl

lemma canonicalFrameSection_affine (t : SectionIndex) (ht : Good t) :
    canonicalFrameSection t ht = ActualSections.affineSection (coefficientChart t)
      (coefficientIota t ht) canonicalSheaf _ (coefficientCanonicalIso t ht)
      (coefficientCanonicalGenerator t ht) := by
  unfold canonicalFrameSection ActualCotangent.topChartSection
  rw [← coefficientCanonicalIso_eq_top]
  rfl

lemma canonicalFrameSection_chartFrame (t : SectionIndex) (ht : Good t) :
    canonicalFrameSection t ht =
      chartFrame (coefficientIota t ht) (coefficientCanonicalUnitIso t ht) := by
  rw [canonicalFrameSection_affine]
  exact (affineUnit_chartFrame (coefficientChart t) (coefficientIota t ht) canonicalSheaf
    _ (coefficientCanonicalIso t ht) (coefficientCanonicalFrame t ht).toModuleIso).symm

instance canonicalFrameSection_isIso (t : SectionIndex) (ht : Good t) :
    IsIso (overFromSection canonicalSheaf (coefficientIota t ht ''ᵁ ⊤)
      (canonicalFrameSection t ht)) := by
  rw [canonicalFrameSection_chartFrame]
  exact chartFrame_isIso (coefficientIota t ht) (coefficientCanonicalUnitIso t ht)

def canonicalOpenUnitIso (t : SectionIndex) (ht : Good t) :
    canonicalSheaf.over (coefficientIota t ht ''ᵁ ⊤) ≅
      SheafOfModules.unit (projectiveSurface.ringCatSheaf.over (coefficientIota t ht ''ᵁ ⊤)) :=
  (asIso (overFromSection canonicalSheaf (coefficientIota t ht ''ᵁ ⊤)
    (canonicalFrameSection t ht))).symm
lemma canonicalOpenUnitIso_frame (t : SectionIndex) (ht : Good t)
    (V : projectiveSurface.Opens) (h : V ≤ coefficientIota t ht ''ᵁ ⊤) :
    frame (canonicalOpenUnitIso t ht) V h =
      canonicalSheaf.val.map (homOfLE h).op (canonicalFrameSection t ht) :=
  overFromSection_frame (canonicalFrameSection t ht) V h
end SourceSymmetry

end

/-! Sections are determined by their pullbacks to an open cover. -/
noncomputable section
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualSections
universe u
variable {X : Scheme.{u}} {ι : Type*} (Y : ι → Scheme.{u})
  (j : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (j i)]
  (hc : (⨆ i, (j i).opensRange) = ⊤)
include hc in
lemma section_eq_of_appTop {a b : Γ(X,⊤)}
    (h : ∀ i, (j i).appTop a = (j i).appTop b) : a = b := by
  apply X.IsSheaf.section_ext
  intro x hx
  have hx' : x ∈ ⨆ i, (j i).opensRange := by rw [hc]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx'
  refine ⟨(j i) ''ᵁ ⊤, le_top, ?_, ?_⟩
  · simpa only [Scheme.Hom.image_top_eq_opensRange] using hi
  · apply (ConcreteCategory.bijective_of_isIso ((j i).appIso ⊤).hom).1
    have he : X.presheaf.map (homOfLE (show (j i) ''ᵁ ⊤ ≤ ⊤ from le_top)).op ≫
        ((j i).appIso ⊤).hom = (j i).appTop := by
      rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]
      erw [Scheme.Hom.appLE_eq_app]
    simpa only [← ConcreteCategory.comp_apply, he] using h i
end ActualSections

end

/-! Degree-one elements of the section ring give sections of the exceptional ideal. -/
noncomputable section
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace AlgebraicGeometry.Scheme
open scoped _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme
universe u
variable {X Y Z : _root_.AlgebraicGeometry.Scheme.{u}} {R B : Type u} [CommRing R] [CommRing B]
lemma coordinateMap_precomp_apply (α : Z ⟶ Y) (f : Y ⟶ _root_.AlgebraicGeometry.Spec (.of R)) (a : R) :
    coordinateMap (α ≫ f) a = α.appTop (coordinateMap f a) :=
  RingHom.congr_fun (coordinateMap_precomp α f) a
lemma coordinateMap_spec (φ : R →+* B) :
    coordinateMap (_root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ)) =
      (_root_.AlgebraicGeometry.Scheme.ΓSpecIso (.of B)).inv.hom.comp φ := by
  unfold coordinateMap
  rw [← _root_.AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality]
  rfl
lemma coordinateMap_ideal_of_cover {ι : Type*} (U : ι → _root_.AlgebraicGeometry.Scheme.{u})
    (j : ∀ i, U i ⟶ X) [∀ i, _root_.AlgebraicGeometry.IsOpenImmersion (j i)]
    (hc : (⨆ i, (j i).opensRange) = ⊤)
    (f : X ⟶ Y) (g : Y ⟶ _root_.AlgebraicGeometry.Spec (.of R)) (a : R)
    (h : ∀ i, coordinateMap (j i ≫ f ≫ g) a = 0) :
    f.app ⊤ (coordinateMap g a) = 0 := by
  apply ActualSections.section_eq_of_appTop U j hc
  intro i
  erw [map_zero]
  change (j i).appTop (f.appTop (coordinateMap g a)) = 0
  exact (congrArg (j i).appTop (coordinateMap_precomp_apply f g a)).symm.trans
    ((coordinateMap_precomp_apply (j i) (f ≫ g) a).symm.trans (h i))
end AlgebraicGeometry.Scheme
namespace SourcePullbackChart
open KummerSourceModel SourceZeroSections SectionCompletion
attribute [local instance] integralSurfaceCommRing integralSurfaceSemiring
  integralPullbackCommRing integralPullbackSemiring pullbackBaseAlgebra surfaceOriginAlgebra
  completedPullbackModule completedPullbackAction completedPullbackSMul completedPullbackTower
  completedSurfaceModule completedSeriesModule completedSourceChartCommRing completedSourceChartSemiring
  completedSourceAlgebra
  originChartCommRing originChartSemiring originPlaneCommRing originPlaneSemiring
  chartBaseAlgebra planeOriginAlgebra baseChartModule baseChartAction baseChartSMul baseChartTower
  planeOriginModule completedBlowupCommRing completedBlowupSemiring completedBlowupAlgebra

def degreeOneFunction (c : ExplicitCone.L) (hc : c ∈ ExplicitCone.pieces 1) : Γ(W,⊤) :=
  Scheme.coordinateMap (SourceConeMorphism.forgetCompletion ≫ coneMorphism)
    (linearSection ExplicitCone.pieces c hc)

lemma degreeOneFunction_vanishes (c : ExplicitCone.L) (hc : c ∈ ExplicitCone.pieces 1) :
    completedSourceZero.app ⊤ (degreeOneFunction c hc) = 0 := by
  apply Scheme.coordinateMap_ideal_of_cover
    (fun i : Fin 3 => Spec (.of (surfaceChart i))) surfaceIota surfaceIota_cover
    completedSourceZero (SourceConeMorphism.forgetCompletion ≫ coneMorphism)
    (linearSection ExplicitCone.pieces c hc)
  intro i
  rw [← Category.assoc completedSourceZero,
    completedSourceZero_forget, ← Category.assoc, surfaceIota_sourceZero,
    Category.assoc, pullbackIota_coneMorphism, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, Scheme.coordinateMap_spec]
  change (Scheme.ΓSpecIso (.of (surfaceChart i))).inv
    (pullbackZeroEvaluation i (coneEvaluation i
      (linearSection ExplicitCone.pieces c hc))) = 0
  rw [coneEvaluation_homogeneous i 1 _ (linearSection_homogeneous ExplicitCone.pieces c hc),
    map_mul, map_pow, pullbackZeroEvaluation_fiber, zero_pow (by decide : 1 ≠ 0),
    mul_zero, map_zero]

/-- degree-one global section of the Cartier ideal. -/
def degreeOneIdealGenerator (c : ExplicitCone.L) (hc : c ∈ ExplicitCone.pieces 1) :
    SheafOfModules.unit W.ringCatSheaf ⟶ ActualCartier.idealSheaf completedSourceZero :=
  ActualCartier.idealGenerator completedSourceZero (degreeOneFunction c hc)
    (degreeOneFunction_vanishes c hc)

/-- Degree-one section of the conormal line on the source X. -/
def degreeOneConormalGenerator (c : ExplicitCone.L) (hc : c ∈ ExplicitCone.pieces 1) :
    SheafOfModules.unit ExplicitCone.projectiveSurface.ringCatSheaf ⟶
      (Scheme.Modules.pullback completedSourceZero).obj
        (ActualCartier.idealSheaf completedSourceZero) :=
  (ActualSheafTensor.sheafPullbackUnitIso completedSourceZero).inv ≫
    (Scheme.Modules.pullback completedSourceZero).map (degreeOneIdealGenerator c hc)
end SourcePullbackChart

end

/-! Local equations for degree-one sections of the exceptional ideal. -/
noncomputable section
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite TensorProduct
namespace SourcePullbackChart
open KummerSourceModel SourceZeroSections SectionCompletion
  Scheme.Modules ActualCartier ActualSections ActualSheafTensor
attribute [local instance] integralSurfaceCommRing integralSurfaceSemiring
  integralPullbackCommRing integralPullbackSemiring pullbackBaseAlgebra surfaceOriginAlgebra
  completedPullbackModule completedPullbackAction completedPullbackSMul completedPullbackTower
  completedSurfaceModule completedSeriesModule completedSourceChartCommRing completedSourceChartSemiring
  completedSourceAlgebra
  originChartCommRing originChartSemiring originPlaneCommRing originPlaneSemiring
  chartBaseAlgebra planeOriginAlgebra baseChartModule baseChartAction baseChartSMul baseChartTower
  planeOriginModule completedBlowupCommRing completedBlowupSemiring completedBlowupAlgebra

def degreeOneCoefficient (i : Fin 3) (c : ExplicitCone.L) (hc : c ∈ ExplicitCone.pieces 1) :
    surfaceChart i :=
  dehomogenize ExplicitCone.pieces (ExplicitCone.projectiveParameter i)
    (ExplicitCone.projectiveParameter_mem i) (ExplicitCone.projectiveParameter_ne_zero i)
    (linearSection ExplicitCone.pieces c hc)

lemma degreeOneCoefficient_self (i : Fin 3) :
    degreeOneCoefficient i (ExplicitCone.projectiveParameter i)
      (ExplicitCone.projectiveParameter_mem i) = 1 := by
  apply homogeneousChartMap_injective ExplicitCone.pieces (ExplicitCone.projectiveParameter i)
    (ExplicitCone.projectiveParameter_mem i) (ExplicitCone.projectiveParameter_ne_zero i)
  rw [degreeOneCoefficient, homogeneousChartMap_dehomogenize, map_one,
    evaluateInv_homogeneous _ _ 1 _ (linearSection_homogeneous _ _ _)]
  simp only [linearSection, Polynomial.coeff_monomial, ite_true, pow_one,
    div_self (ExplicitCone.projectiveParameter_ne_zero i)]

def completedDegreeOneCoefficient (i : Fin 3) (c : ExplicitCone.L)
    (hc : c ∈ ExplicitCone.pieces 1) : completedSourceChart i :=
  surfaceIn i (degreeOneCoefficient i c hc) ⊗ₜ[S] (1 : A)

lemma degreeOneFunction_chart (i : Fin 3) (c : ExplicitCone.L)
    (hc : c ∈ ExplicitCone.pieces 1) :
    (completedIota i).appTop (degreeOneFunction c hc) =
      (Scheme.ΓSpecIso (.of (completedSourceChart i))).inv
        (completedDegreeOneCoefficient i c hc * completedFiberParameter i) := by
  have he := (Scheme.coordinateMap_precomp_apply (completedIota i)
    (SourceConeMorphism.forgetCompletion ≫ coneMorphism)
    (linearSection ExplicitCone.pieces c hc)).symm
  change (completedIota i).appTop (degreeOneFunction c hc) = _ at he
  rw [← Category.assoc, completedIota_forget, Category.assoc, pullbackIota_coneMorphism,
    completedChartFirst, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    Scheme.coordinateMap_spec] at he
  refine he.trans ?_
  change (Scheme.ΓSpecIso (.of (completedSourceChart i))).inv
    (coneEvaluation i (linearSection ExplicitCone.pieces c hc) ⊗ₜ[S] (1 : A)) = _
  rw [coneEvaluation_homogeneous i 1 _ (linearSection_homogeneous _ _ _), pow_one]
  congr 1
  change (surfaceIn i (degreeOneCoefficient i c hc) * fiberParameter i) ⊗ₜ[S] (1 : A) =
    (surfaceIn i (degreeOneCoefficient i c hc) ⊗ₜ[S] (1 : A)) * (fiberParameter i ⊗ₜ[S] (1 : A))
  exact (Algebra.TensorProduct.includeLeft : pullbackChart i →ₐ[S] completedSourceChart i).map_mul
    (surfaceIn i (degreeOneCoefficient i c hc)) (fiberParameter i)

lemma degreeOneParameter_chart (i : Fin 3) :
    (completedIota i).appTop
      (degreeOneFunction (ExplicitCone.projectiveParameter i) (ExplicitCone.projectiveParameter_mem i)) =
      (Scheme.ΓSpecIso (.of (completedSourceChart i))).inv (completedFiberParameter i) := by
  rw [degreeOneFunction_chart, completedDegreeOneCoefficient, degreeOneCoefficient_self,
    map_one]
  change (Scheme.ΓSpecIso (.of (completedSourceChart i))).inv (1 * completedFiberParameter i) = _
  rw [one_mul]

lemma degreeOneFunction_chart_ratio (i : Fin 3) (c : ExplicitCone.L)
    (hc : c ∈ ExplicitCone.pieces 1) :
    (completedIota i).appTop (degreeOneFunction c hc) =
      (Scheme.ΓSpecIso (.of (completedSourceChart i))).inv (completedDegreeOneCoefficient i c hc) *
        (completedIota i).appTop
          (degreeOneFunction (ExplicitCone.projectiveParameter i)
            (ExplicitCone.projectiveParameter_mem i)) := by
  rw [degreeOneFunction_chart, degreeOneParameter_chart, map_mul]

lemma degreeOneParameterIdeal_chart_isIso (i : Fin 3) :
    IsIso ((restrictFunctor (completedIota i)).map
      (degreeOneIdealGenerator (ExplicitCone.projectiveParameter i)
        (ExplicitCone.projectiveParameter_mem i))) := by
  have : (idealSheaf completedSourceZero).IsFinitePresentation := idealSheaf_coherent _
  have : ((restrictFunctor (completedIota i)).obj (idealSheaf completedSourceZero)).IsFinitePresentation :=
    CoherentGlobal.coherent_restrict _ _
  have hi := chartGenerator_isIso completedSourceZero (completedZeroChart i)
    (surfaceIota i) (completedIota i) (surfaceIota_completedSourceZero i)
    (by simpa only [Scheme.Hom.image_top_eq_opensRange] using (surfaceZero_chart_preimage i).symm)
    (degreeOneFunction (ExplicitCone.projectiveParameter i) (ExplicitCone.projectiveParameter_mem i))
    (degreeOneFunction_vanishes _ _)
    (by rw [degreeOneParameter_chart]; exact specInverse_regular _ (completedFiberParameter_regular i))
    (by rw [degreeOneParameter_chart]; exact specMap_app_kernel _ _ (completedZeroEvaluation_kernel i))
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _
    (restrictUnitIso (completedIota i)).isIso_inv hi

lemma completedDegreeOneCoefficient_residue (i : Fin 3) (c : ExplicitCone.L)
    (hc : c ∈ ExplicitCone.pieces 1) :
    completedZeroEvaluation i (completedDegreeOneCoefficient i c hc) =
      degreeOneCoefficient i c hc := by
  rw [completedDegreeOneCoefficient, completedZeroEvaluation_tmul, map_one, map_one,
    mul_one, pullbackZeroEvaluation_surface]

end SourcePullbackChart

end

/-! Transport of section ratios across commuting affine open charts. -/
noncomputable section
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualSections
open Scheme.Modules ActualSheafTensor
variable {X : Scheme.{0}}
private lemma map_ratio_of_commute {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {U V W : C} {Q : D} (l : Q ⟶ F.obj U)
    (a : U ⟶ U) (b : Q ⟶ Q) (p : U ⟶ V) (s t : V ⟶ W)
    (h : p ≫ s = a ≫ p ≫ t) (hc : l ≫ F.map a = b ≫ l) :
    (l ≫ F.map p) ≫ F.map s = b ≫ (l ≫ F.map p) ≫ F.map t := by
  calc
    (l ≫ F.map p) ≫ F.map s = l ≫ F.map (p ≫ s) := by
      rw [F.map_comp, Category.assoc]
    _ = l ≫ F.map (a ≫ p ≫ t) := congrArg (fun z => l ≫ F.map z) h
    _ = (l ≫ F.map a) ≫ (F.map p ≫ F.map t) := by
      rw [F.map_comp, F.map_comp, Category.assoc]
    _ = (b ≫ l) ≫ (F.map p ≫ F.map t) := congrArg (· ≫ (F.map p ≫ F.map t)) hc
    _ = b ≫ (l ≫ F.map p) ≫ F.map t := by simp only [Category.assoc]

lemma unit_scalar_comm (a : Γ(X,⊤))
    (u : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) :
    u ≫ scalar a = scalar a ≫ u := by
  apply unitHom_ext_top
  change (scalar a).val.app (op ⊤) (u.val.app (op ⊤) (1 : Γ(X,⊤))) =
    u.val.app (op ⊤) ((scalar a).val.app (op ⊤) (1 : Γ(X,⊤)))
  erw [fromUnit_top, fromUnit_top, one_smul]
  let v : Γ(X,⊤) →ₗ[Γ(X,⊤)] Γ(X,⊤) := (u.val.app (op ⊤)).hom
  change v 1 * a = v a
  have hu := v.map_smul a 1
  change v (a * 1) = a * v 1 at hu
  simpa only [mul_one, mul_comm] using hu.symm

universe v
variable {C : Type v} [Category C]
lemma ratio_across_natIso (F G : C ⥤ X.Modules) (e : F ≅ G) {D M : C}
    (s t : D ⟶ M)
    (p : SheafOfModules.unit X.ringCatSheaf ⟶ F.obj D)
    (q : SheafOfModules.unit X.ringCatSheaf ≅ G.obj D) (a : Γ(X,⊤))
    (h : q.hom ≫ G.map s = scalar a ≫ q.hom ≫ G.map t) :
    p ≫ F.map s = scalar a ≫ p ≫ F.map t := by
  apply (cancel_mono (e.app M).hom).mp
  change p ≫ (F.map s ≫ e.hom.app M) = scalar a ≫ p ≫ (F.map t ≫ e.hom.app M)
  erw [e.hom.naturality s, e.hom.naturality t]
  let u := p ≫ (e.app D).hom ≫ q.inv
  have hu : u ≫ q.hom = p ≫ (e.app D).hom := by
    dsimp only [u]
    erw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  calc
    p ≫ (e.app D).hom ≫ G.map s = u ≫ q.hom ≫ G.map s := by
      erw [← Category.assoc u, hu]
      erw [Category.assoc]
    _ = u ≫ scalar a ≫ q.hom ≫ G.map t := by erw [h]
    _ = scalar a ≫ u ≫ q.hom ≫ G.map t := by
      erw [← Category.assoc u, unit_scalar_comm]
      erw [Category.assoc]
    _ = scalar a ≫ p ≫ (e.app D).hom ≫ G.map t := by
      erw [← Category.assoc u, hu]
      erw [Category.assoc]

end ActualSections

namespace ActualChartPullback
open Scheme.Modules ActualSections ActualSheafTensor
variable {A B C D : Scheme.{0}}
  (j : C ⟶ A) (f : A ⟶ B) (q : C ⟶ D) (k : D ⟶ B)
  [IsOpenImmersion j] [IsOpenImmersion k] (h : j ≫ f = q ≫ k)

include h in
lemma section_ratio {M : B.Modules}
    (s t : SheafOfModules.unit B.ringCatSheaf ⟶ M) (a : Γ(D,⊤))
    (hr : (restrictUnitIso k).inv ≫ (restrictFunctor k).map s =
      scalar a ≫ (restrictUnitIso k).inv ≫ (restrictFunctor k).map t) :
    (restrictUnitIso j).inv ≫ (restrictFunctor j).map
        ((sheafPullbackUnitIso f).inv ≫ (Scheme.Modules.pullback f).map s) =
    scalar (q.appTop a) ≫ (restrictUnitIso j).inv ≫ (restrictFunctor j).map
        ((sheafPullbackUnitIso f).inv ≫ (Scheme.Modules.pullback f).map t) := by
  let e := (sheafPullbackUnitIso q).symm ≪≫
    (Scheme.Modules.pullback q).mapIso (restrictUnitIso k).symm
  have he : e.hom ≫ (restrictFunctor k ⋙ Scheme.Modules.pullback q).map s =
      scalar (q.appTop a) ≫ e.hom ≫
        (restrictFunctor k ⋙ Scheme.Modules.pullback q).map t := by
    exact map_ratio_of_commute (Scheme.Modules.pullback q) (sheafPullbackUnitIso q).inv
      (scalar a) (scalar (q.appTop a)) (restrictUnitIso k).inv
      ((restrictFunctor k).map s) ((restrictFunctor k).map t) hr
      (pullback_scalar_inv q a)
  have hh := ratio_across_natIso
    (Scheme.Modules.pullback f ⋙ restrictFunctor j)
    (restrictFunctor k ⋙ Scheme.Modules.pullback q) (squareIso j f q k h)
    s t ((restrictUnitIso j).inv ≫ (restrictFunctor j).map (sheafPullbackUnitIso f).inv)
    e (q.appTop a) he
  let F : A.Modules ⥤ C.Modules := restrictFunctor j
  let l := (restrictUnitIso j).inv
  let p := (sheafPullbackUnitIso f).inv
  let u := (Scheme.Modules.pullback f).map s
  let v := (Scheme.Modules.pullback f).map t
  let b := scalar (q.appTop a)
  exact (congrArg (l ≫ ·) (F.map_comp p u)).trans
    ((Category.assoc l (F.map p) (F.map u)).symm.trans
      (hh.trans
        ((congrArg (b ≫ ·) (Category.assoc l (F.map p) (F.map v))).trans
          (congrArg (fun z => b ≫ l ≫ z) (F.map_comp p v).symm))))
end ActualChartPullback

end

/-! Open restriction preserves section ratios and frames. -/
noncomputable section
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualSections
open Scheme.Modules ActualSheafTensor
variable {X Y : Scheme.{0}} (j : X ⟶ Y) [IsOpenImmersion j]
lemma restrict_scalar_inv (a : Γ(Y,⊤)) :
    (restrictUnitIso j).inv ≫ (restrictFunctor j).map (scalar a) =
      scalar (j.appTop a) ≫ (restrictUnitIso j).inv := by
  have : Mono (restrictUnitIso j).hom :=
    @IsIso.mono_of_iso _ _ _ _ _ (restrictUnitIso j).isIso_hom
  apply (cancel_mono (restrictUnitIso j).hom).mp
  erw [Category.assoc (restrictUnitIso j).inv,
    Category.assoc (scalar (j.appTop a)), Iso.inv_hom_id, Category.comp_id]
  apply unitHom_ext_top
  erw [restrictScalar_top]
  change j.appTop a * 1 = _
  erw [fromUnit_top, mul_one, one_smul]

lemma scalar_isIso (a : Γ(X,⊤)) (ha : IsUnit a) : IsIso (scalar a) := by
  obtain ⟨u, rfl⟩ := ha
  refine ⟨⟨scalar (↑u⁻¹ : Γ(X,⊤)), ?_, ?_⟩⟩ <;>
    apply unitHom_ext_top <;>
    simp only [SheafOfModules.comp_val]
  · change (scalar (↑u⁻¹ : Γ(X,⊤))).val.app (op ⊤)
        ((scalar (↑u : Γ(X,⊤))).val.app (op ⊤) (1 : Γ(X,⊤))) = (1 : Γ(X,⊤))
    erw [fromUnit_top, fromUnit_top, one_smul]
    exact u.val_inv
  · change (scalar (↑u : Γ(X,⊤))).val.app (op ⊤)
        ((scalar (↑u⁻¹ : Γ(X,⊤))).val.app (op ⊤) (1 : Γ(X,⊤))) = (1 : Γ(X,⊤))
    erw [fromUnit_top, fromUnit_top, one_smul]
    exact u.inv_val

lemma scalar_comp_congr {Z : Scheme.{0}} {M : Z.Modules}
    {a b : Γ(Z,⊤)} (h : a = b) (s : SheafOfModules.unit Z.ringCatSheaf ⟶ M) :
    scalar a ≫ s = scalar b ≫ s := by subst h; rfl

end ActualSections
namespace ActualChartPullback
open Scheme.Modules ActualSections ActualSheafTensor
variable {A B C D : Scheme.{0}}
  (j : C ⟶ A) (f : A ⟶ B) (q : C ⟶ D) (k : D ⟶ B)
  [IsOpenImmersion j] [IsOpenImmersion k] (h : j ≫ f = q ≫ k)
include h in
lemma section_ratio_eq {M : B.Modules}
    (s t : SheafOfModules.unit B.ringCatSheaf ⟶ M) (a : Γ(D,⊤)) (b : Γ(C,⊤))
    (hab : q.appTop a = b)
    (hr : (restrictUnitIso k).inv ≫ (restrictFunctor k).map s =
      scalar a ≫ (restrictUnitIso k).inv ≫ (restrictFunctor k).map t) :
    (restrictUnitIso j).inv ≫ (restrictFunctor j).map
        ((sheafPullbackUnitIso f).inv ≫ (Scheme.Modules.pullback f).map s) =
    scalar b ≫ (restrictUnitIso j).inv ≫ (restrictFunctor j).map
        ((sheafPullbackUnitIso f).inv ≫ (Scheme.Modules.pullback f).map t) := by
  simpa only [hab] using section_ratio j f q k h s t a hr

include h in
lemma section_isIso {M : B.Modules} (s : SheafOfModules.unit B.ringCatSheaf ⟶ M)
    [IsIso ((restrictFunctor k).map s)] :
    IsIso ((restrictUnitIso j).inv ≫ (restrictFunctor j).map
      ((sheafPullbackUnitIso f).inv ≫ (Scheme.Modules.pullback f).map s)) := by
  have hs := map_isIso j f q k h s
  have hu : IsIso ((restrictFunctor j).map (sheafPullbackUnitIso f).inv) :=
    ((restrictFunctor j).mapIso (sheafPullbackUnitIso f).symm).isIso_hom
  erw [Functor.map_comp]
  exact IsIso.comp_isIso' (restrictUnitIso j).isIso_inv (IsIso.comp_isIso' hu hs)
end ActualChartPullback

end

/-! Degree-one conormal sections and their projective ratios. -/
noncomputable section
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite TensorProduct
namespace SourcePullbackChart
open KummerSourceModel SourceZeroSections SectionCompletion
  Scheme.Modules ActualCartier ActualSections ActualSheafTensor
attribute [local instance] integralSurfaceCommRing integralSurfaceSemiring
  integralPullbackCommRing integralPullbackSemiring pullbackBaseAlgebra surfaceOriginAlgebra
  completedPullbackModule completedPullbackAction completedPullbackSMul completedPullbackTower
  completedSurfaceModule completedSeriesModule completedSourceChartCommRing completedSourceChartSemiring
  completedSourceAlgebra

def degreeOneConormalChartSection (i : Fin 3) (c : ExplicitCone.L)
    (hc : c ∈ ExplicitCone.pieces 1) :
    SheafOfModules.unit (Spec (.of (surfaceChart i))).ringCatSheaf ⟶
      (restrictFunctor (surfaceIota i)).obj
        ((Scheme.Modules.pullback completedSourceZero).obj (idealSheaf completedSourceZero)) :=
  (restrictUnitIso (surfaceIota i)).inv ≫
    (restrictFunctor (surfaceIota i)).map (degreeOneConormalGenerator c hc)

lemma degreeOneParameterConormal_chart_isIso (i : Fin 3) :
    IsIso (degreeOneConormalChartSection i (ExplicitCone.projectiveParameter i)
      (ExplicitCone.projectiveParameter_mem i)) := by
  have := degreeOneParameterIdeal_chart_isIso i
  exact ActualChartPullback.section_isIso (surfaceIota i) completedSourceZero (completedZeroChart i)
    (completedIota i) (surfaceIota_completedSourceZero i)
    (degreeOneIdealGenerator (ExplicitCone.projectiveParameter i)
      (ExplicitCone.projectiveParameter_mem i))

lemma zeroChart_degreeOneCoefficient (i : Fin 3) (c : ExplicitCone.L)
    (hc : c ∈ ExplicitCone.pieces 1) :
    (completedZeroChart i).appTop
      ((Scheme.ΓSpecIso (.of (completedSourceChart i))).inv (completedDegreeOneCoefficient i c hc)) =
    (Scheme.ΓSpecIso (.of (surfaceChart i))).inv (degreeOneCoefficient i c hc) := by
  have he := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (completedZeroEvaluation i))).symm (completedDegreeOneCoefficient i c hc)
  change (completedZeroChart i).appTop _ = _ at he
  exact he.trans (congrArg (Scheme.ΓSpecIso (.of (surfaceChart i))).inv
    (completedDegreeOneCoefficient_residue i c hc))

end SourcePullbackChart

end

noncomputable section
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite TensorProduct
namespace SourcePullbackChart
open KummerSourceModel SourceZeroSections SectionCompletion
  Scheme.Modules ActualCartier ActualSections ActualSheafTensor
attribute [local instance] integralSurfaceCommRing integralSurfaceSemiring
  integralPullbackCommRing integralPullbackSemiring pullbackBaseAlgebra surfaceOriginAlgebra
  completedPullbackModule completedPullbackAction completedPullbackSMul completedPullbackTower
  completedSurfaceModule completedSeriesModule completedSourceChartCommRing completedSourceChartSemiring
  completedSourceAlgebra

lemma degreeOneConormalChartSection_ratio (i : Fin 3) (c : ExplicitCone.L)
    (hc : c ∈ ExplicitCone.pieces 1) :
    degreeOneConormalChartSection i c hc =
      scalar ((Scheme.ΓSpecIso (.of (surfaceChart i))).inv (degreeOneCoefficient i c hc)) ≫
        degreeOneConormalChartSection i (ExplicitCone.projectiveParameter i)
          (ExplicitCone.projectiveParameter_mem i) := by
  have hr := chartGenerator_ratio completedSourceZero (completedIota i)
    (degreeOneFunction (ExplicitCone.projectiveParameter i) (ExplicitCone.projectiveParameter_mem i))
    (degreeOneFunction c hc) (degreeOneFunction_vanishes _ _) (degreeOneFunction_vanishes _ _)
    _ (degreeOneFunction_chart_ratio i c hc)
  exact ActualChartPullback.section_ratio_eq (surfaceIota i) completedSourceZero
    (completedZeroChart i) (completedIota i) (surfaceIota_completedSourceZero i)
    (degreeOneIdealGenerator c hc)
    (degreeOneIdealGenerator (ExplicitCone.projectiveParameter i) (ExplicitCone.projectiveParameter_mem i))
    ((Scheme.ΓSpecIso (.of (completedSourceChart i))).inv (completedDegreeOneCoefficient i c hc))
    ((Scheme.ΓSpecIso (.of (surfaceChart i))).inv (degreeOneCoefficient i c hc))
    (zeroChart_degreeOneCoefficient i c hc) hr
end SourcePullbackChart

end

/-! Locality of line-section isomorphisms over scheme open covers. -/
noncomputable section
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualSections
open Scheme.Modules
lemma isUnit_appTop_of_range {X Y : Scheme.{0}} (j : X ⟶ Y)
    (a : Γ(Y,⊤)) (ha : ∀ x : X, j x ∈ Y.basicOpen a) : IsUnit (j.appTop a) := by
  apply X.toRingedSpace.isUnit_of_isUnit_germ ⊤ (j.appTop a)
  intro x hx
  apply (Scheme.mem_basicOpen X (j.appTop a) x hx).mp
  rw [← j.preimage_basicOpen_top]
  exact ha x

lemma restrict_scalar_isIso {X Y : Scheme.{0}} (j : X ⟶ Y) [IsOpenImmersion j]
    (a : Γ(Y,⊤)) (ha : IsUnit (j.appTop a)) :
    IsIso ((restrictFunctor j).map (scalar a)) := by
  have hs := scalar_isIso (j.appTop a) ha
  have he := restrict_scalar_inv j a
  have hi : IsIso ((restrictUnitIso j).inv ≫ (restrictFunctor j).map (scalar a)) :=
    he.symm ▸ IsIso.comp_isIso' hs (restrictUnitIso j).isIso_inv
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ (restrictUnitIso j).isIso_inv hi

lemma isIso_of_openImmersion_cover {Y : Scheme.{0}} {ι : Type} (X : ι → Scheme.{0})
    (j : ∀ i, X i ⟶ Y) [∀ i, IsOpenImmersion (j i)]
    (hc : (⨆ i, (j i).opensRange) = ⊤) {M N : Y.Modules} (f : M ⟶ N)
    (hf : ∀ i, IsIso ((restrictFunctor (j i)).map f)) : IsIso f := by
  apply CoherentGlobal.isIso_of_open_cover (fun i => (j i).opensRange) hc f
  intro i
  have := hf i
  let e := (restrictFunctorComp (j i).isoOpensRange.inv (j i)).symm ≪≫
    restrictFunctorCongr (Scheme.Hom.isoOpensRange_inv_comp (j i))
  have hx : IsIso ((restrictFunctor (j i) ⋙ restrictFunctor (j i).isoOpensRange.inv).map f) := by
    change IsIso ((restrictFunctor (j i).isoOpensRange.inv).map ((restrictFunctor (j i)).map f))
    infer_instance
  exact (NatIso.isIso_map_iff e f).mp hx

lemma restrict_cover_range {Y : Scheme.{0}} {ι : Type} (X : ι → Scheme.{0})
    (j : ∀ i, X i ⟶ Y) [∀ i, IsOpenImmersion (j i)]
    (hc : (⨆ i, (j i).opensRange) = ⊤) (U : Y.Opens) :
    (⨆ i, (j i ∣_ U).opensRange) = ⊤ := by
  have hp (i) : (j i ∣_ U).opensRange = U.ι ⁻¹ᵁ (j i).opensRange := by
    dsimp only [morphismRestrict]
    rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Hom.opensRange_pullbackSnd]
  simp_rw [hp]
  rw [← Scheme.Hom.preimage_iSup, hc, Scheme.Hom.preimage_top]

lemma isIso_restrict_of_local_frames {Y : Scheme.{0}} {ι : Type} (X : ι → Scheme.{0})
    (j : ∀ i, X i ⟶ Y) [∀ i, IsOpenImmersion (j i)]
    (hc : (⨆ i, (j i).opensRange) = ⊤) (U : Y.Opens)
    {M : Y.Modules} (s : SheafOfModules.unit Y.ringCatSheaf ⟶ M)
    (t : ∀ i, SheafOfModules.unit (X i).ringCatSheaf ⟶ (restrictFunctor (j i)).obj M)
    (a : ∀ i, Γ(X i,⊤)) (ht : ∀ i, IsIso (t i))
    (hr : ∀ i, (restrictUnitIso (j i)).inv ≫ (restrictFunctor (j i)).map s =
      scalar (a i) ≫ t i)
    (hu : ∀ i, j i ⁻¹ᵁ U ≤ (X i).basicOpen (a i)) :
    IsIso ((restrictFunctor U.ι).map s) := by
  apply isIso_of_openImmersion_cover (fun i => (j i ⁻¹ᵁ U).toScheme)
    (fun i => j i ∣_ U) (restrict_cover_range X j hc U)
  intro i
  let F := restrictFunctor (j i ⁻¹ᵁ U).ι
  have hs : IsIso (F.map ((restrictFunctor (j i)).map s)) := by
    have hau : IsUnit ((j i ⁻¹ᵁ U).ι.appTop (a i)) :=
      isUnit_appTop_of_range (j i ⁻¹ᵁ U).ι (a i) (fun x => hu i x.property)
    have ha : IsIso (F.map (scalar (a i))) :=
      restrict_scalar_isIso (j i ⁻¹ᵁ U).ι (a i) hau
    have ht' : IsIso (F.map (t i)) := (F.mapIso (@asIso _ _ _ _ _ (ht i))).isIso_hom
    have hh : F.map (restrictUnitIso (j i)).inv ≫ F.map ((restrictFunctor (j i)).map s) =
        F.map (scalar (a i)) ≫ F.map (t i) :=
      (F.map_comp _ _).symm.trans ((congrArg F.map (hr i)).trans (F.map_comp _ _))
    have hm : IsIso (F.map (restrictUnitIso (j i)).inv ≫
        F.map ((restrictFunctor (j i)).map s)) :=
      hh.symm ▸ IsIso.comp_isIso' ha ht'
    exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _
      (F.mapIso (restrictUnitIso (j i)).symm).isIso_hom hm
  let e := (restrictFunctorComp (j i ∣_ U) U.ι).symm ≪≫
    restrictFunctorCongr (morphismRestrict_ι (j i) U) ≪≫
      restrictFunctorComp (j i ⁻¹ᵁ U).ι (j i)
  exact (NatIso.isIso_map_iff e s).mpr hs
end ActualSections

end

/-! A degree-one conormal section is a frame on its projective basic open. -/
noncomputable section
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace SourcePullbackChart
open ExplicitCone KummerSourceModel SourceZeroSections SectionCompletion
  Scheme.Modules ActualCartier ActualSections ActualSheafTensor
attribute [local instance] integralSurfaceCommRing integralSurfaceSemiring
  integralPullbackCommRing integralPullbackSemiring pullbackBaseAlgebra surfaceOriginAlgebra
  completedPullbackModule completedPullbackAction completedPullbackSMul completedPullbackTower
  completedSurfaceModule completedSeriesModule completedSourceChartCommRing completedSourceChartSemiring
  completedSourceAlgebra

lemma surfaceChart_degreeOne_open (i : Fin 3) (c : L) (hc : c ∈ pieces 1) :
    surfaceIota i ⁻¹ᵁ Proj.basicOpen (homogeneous pieces) (linearSection pieces c hc) =
      (Spec (.of (surfaceChart i))).basicOpen
        ((Scheme.ΓSpecIso (.of (surfaceChart i))).inv (degreeOneCoefficient i c hc)) := by
  rw [basicOpen_eq_of_affine]
  change Proj.awayι (homogeneous pieces) _ _ _ ⁻¹ᵁ
    Proj.basicOpen (homogeneous pieces) (linearSection pieces c hc) = _
  rw [Proj.awayι_preimage_basicOpen (homogeneous pieces) _ _
    (linearSection_homogeneous pieces c hc) (by decide : 0 < 1)]
  congr 1
  rw [degreeOneCoefficient, dehomogenize_linearSection]
  simp only [HomogeneousLocalization.Away.isLocalizationElem, pow_one]

/-- Original conormal generator on its exact Proj nonvanishing locus. -/
lemma degreeOneConormal_isIso_on (c : L) (hc : c ∈ pieces 1) :
    IsIso ((restrictFunctor (Proj.basicOpen (homogeneous pieces) (linearSection pieces c hc)).ι).map
      (degreeOneConormalGenerator c hc)) := by
  apply isIso_restrict_of_local_frames (fun i : Fin 3 => Spec (.of (surfaceChart i)))
    surfaceIota surfaceIota_cover (Proj.basicOpen (homogeneous pieces) (linearSection pieces c hc))
    (degreeOneConormalGenerator c hc)
    (fun i => degreeOneConormalChartSection i (projectiveParameter i) (projectiveParameter_mem i))
    (fun i => (Scheme.ΓSpecIso (.of (surfaceChart i))).inv (degreeOneCoefficient i c hc))
    degreeOneParameterConormal_chart_isIso
  · intro i
    exact degreeOneConormalChartSection_ratio i c hc
  · intro i
    exact le_of_eq (surfaceChart_degreeOne_open i c hc)
end SourcePullbackChart

end

/-! Section ratios are independent of a factorization of an open immersion. -/
noncomputable section
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualSections
open Scheme.Modules
variable {X Y Z : Scheme.{0}}
lemma scalar_mul (a b : Γ(X,⊤)) : scalar (a*b) = scalar a ≫ scalar b := by
  apply unitHom_ext_top
  change (scalar (a*b)).val.app (op ⊤) (1 : Γ(X,⊤)) =
    (scalar b).val.app (op ⊤) ((scalar a).val.app (op ⊤) (1 : Γ(X,⊤)))
  erw [fromUnit_top, fromUnit_top, fromUnit_top, one_smul, one_smul]
  rfl

lemma restrict_ratio_comp (j : X ⟶ Y) (k : Z ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion k] {M : Y.Modules}
    (s t : SheafOfModules.unit Y.ringCatSheaf ⟶ M) (a : Γ(X,⊤))
    (hr : (restrictUnitIso j).inv ≫ (restrictFunctor j).map s =
      scalar a ≫ (restrictUnitIso j).inv ≫ (restrictFunctor j).map t) :
    (restrictUnitIso (k ≫ j)).inv ≫ (restrictFunctor (k ≫ j)).map s =
      scalar (k.appTop a) ≫ (restrictUnitIso (k ≫ j)).inv ≫
        (restrictFunctor (k ≫ j)).map t := by
  let e := (restrictUnitIso k).symm ≪≫ (restrictFunctor k).mapIso (restrictUnitIso j).symm
  have he : e.hom ≫ (restrictFunctor j ⋙ restrictFunctor k).map s =
      scalar (k.appTop a) ≫ e.hom ≫ (restrictFunctor j ⋙ restrictFunctor k).map t := by
    exact map_ratio_of_commute (restrictFunctor k) (restrictUnitIso k).inv
      (scalar a) (scalar (k.appTop a)) (restrictUnitIso j).inv
      ((restrictFunctor j).map s) ((restrictFunctor j).map t) hr
      (restrict_scalar_inv k a)
  exact ratio_across_natIso (restrictFunctor (k ≫ j))
    (restrictFunctor j ⋙ restrictFunctor k) (restrictFunctorComp k j) s t
    (restrictUnitIso (k ≫ j)).inv e (k.appTop a) he

lemma restrict_ratio_of_comp (j : X ⟶ Y) (k : Z ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion k] {M : Y.Modules}
    (s t : SheafOfModules.unit Y.ringCatSheaf ⟶ M) (a : Γ(X,⊤))
    (hr : (restrictUnitIso (k ≫ j)).inv ≫ (restrictFunctor (k ≫ j)).map s =
      scalar (k.appTop a) ≫ (restrictUnitIso (k ≫ j)).inv ≫
        (restrictFunctor (k ≫ j)).map t) :
    (restrictFunctor k).map ((restrictUnitIso j).inv ≫ (restrictFunctor j).map s) =
      (restrictFunctor k).map (scalar a ≫ (restrictUnitIso j).inv ≫ (restrictFunctor j).map t) := by
  let e := (restrictUnitIso k).symm ≪≫ (restrictFunctor k).mapIso (restrictUnitIso j).symm
  have hh := ratio_across_natIso (restrictFunctor j ⋙ restrictFunctor k)
    (restrictFunctor (k ≫ j)) (restrictFunctorComp k j).symm s t e.hom
    (restrictUnitIso (k ≫ j)).symm (k.appTop a) hr
  have : Epi (restrictUnitIso k).inv :=
    @IsIso.epi_of_iso _ _ _ _ _ (restrictUnitIso k).isIso_inv
  apply (cancel_epi (restrictUnitIso k).inv).mp
  erw [Functor.map_comp, Functor.map_comp]
  erw [← Category.assoc (restrictUnitIso k).inv ((restrictFunctor k).map (scalar a)),
    restrict_scalar_inv k a,
    Category.assoc (scalar (k.appTop a)) (restrictUnitIso k).inv]
  exact hh

lemma ratio_of_common_frame {M : X.Modules}
    (s t u : SheafOfModules.unit X.ringCatSheaf ⟶ M) {a b r : Γ(X,⊤)}
    (hs : s = scalar a ≫ u) (ht : t = scalar b ≫ u) (h : a = r*b) :
    s = scalar r ≫ t := by
  erw [hs, h, scalar_mul, Category.assoc, ht]
end ActualSections

end

/-! Homogeneous product charts pull back projective basic-open covers. -/
noncomputable section
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry _root_.HomogeneousLocalization _root_.OAI.HomogeneousLocalization
namespace AlgebraicGeometry.Proj
open scoped _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Proj
variable {σ A : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {f g : A}
  (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1)
def degreeOneLeft : _root_.AlgebraicGeometry.Spec (.of (Away 𝒜 (f*g))) ⟶ _root_.AlgebraicGeometry.Spec (.of (Away 𝒜 f)) :=
  (_root_.AlgebraicGeometry.Proj.pullbackAwayιIso 𝒜 hf (by decide : 0<1) hg (by decide : 0<1) rfl).inv ≫
    CategoryTheory.Limits.pullback.fst _ _
def degreeOneRight : _root_.AlgebraicGeometry.Spec (.of (Away 𝒜 (f*g))) ⟶ _root_.AlgebraicGeometry.Spec (.of (Away 𝒜 g)) :=
  (_root_.AlgebraicGeometry.Proj.pullbackAwayιIso 𝒜 hf (by decide : 0<1) hg (by decide : 0<1) rfl).inv ≫
    CategoryTheory.Limits.pullback.snd _ _
instance degreeOneLeft_open : _root_.AlgebraicGeometry.IsOpenImmersion (degreeOneLeft 𝒜 hf hg) := by
  unfold degreeOneLeft; infer_instance
instance degreeOneRight_open : _root_.AlgebraicGeometry.IsOpenImmersion (degreeOneRight 𝒜 hf hg) := by
  unfold degreeOneRight; infer_instance
lemma degreeOneLeft_eq : degreeOneLeft 𝒜 hf hg =
    _root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom (awayMap 𝒜 hg (rfl : f*g=f*g))) :=
  _root_.AlgebraicGeometry.Proj.pullbackAwayιIso_inv_fst 𝒜 hf (by decide : 0<1) hg (by decide : 0<1) rfl
lemma degreeOneRight_eq : degreeOneRight 𝒜 hf hg =
    _root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom (awayMap 𝒜 hf (mul_comm f g))) :=
  _root_.AlgebraicGeometry.Proj.pullbackAwayιIso_inv_snd 𝒜 hf (by decide : 0<1) hg (by decide : 0<1) rfl
lemma degreeOne_overlap_square :
    degreeOneLeft 𝒜 hf hg ≫ _root_.AlgebraicGeometry.Proj.awayι 𝒜 f hf (by decide : 0<1) =
      degreeOneRight 𝒜 hf hg ≫ _root_.AlgebraicGeometry.Proj.awayι 𝒜 g hg (by decide : 0<1) := by
  simp only [degreeOneLeft, degreeOneRight, Category.assoc, CategoryTheory.Limits.pullback.condition]
lemma degreeOneRight_range : (degreeOneRight 𝒜 hf hg).opensRange =
      _root_.AlgebraicGeometry.Proj.awayι 𝒜 g hg (by decide : 0<1) ⁻¹ᵁ (_root_.AlgebraicGeometry.Proj.awayι 𝒜 f hf (by decide : 0<1)).opensRange := by
  change ((_root_.AlgebraicGeometry.Proj.pullbackAwayιIso 𝒜 hf (by decide : 0<1) hg (by decide : 0<1) rfl).inv ≫
    CategoryTheory.Limits.pullback.snd _ _).opensRange = _
  rw [_root_.AlgebraicGeometry.Scheme.Hom.opensRange_comp_of_isIso, _root_.AlgebraicGeometry.Scheme.Hom.opensRange_pullbackSnd]
lemma degreeOne_intersection_right_cover {I : Type} (f : I → A) (hf : ∀ i, f i ∈ 𝒜 1)
    (hc : (⨆ i, (_root_.AlgebraicGeometry.Proj.awayι 𝒜 (f i) (hf i) (by decide : 0<1)).opensRange) = ⊤) :
    (⨆ i, (degreeOneRight 𝒜 (hf i) hg).opensRange) = ⊤ := by
  simp_rw [degreeOneRight_range]
  rw [← _root_.AlgebraicGeometry.Scheme.Hom.preimage_iSup, hc, _root_.AlgebraicGeometry.Scheme.Hom.preimage_top]
end AlgebraicGeometry.Proj

end

/-! Homogeneous fraction identities on Proj intersections. -/
noncomputable section
namespace HomogeneousLocalization
open scoped _root_.HomogeneousLocalization
open SetLike
variable {σ A : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]
lemma degreeOne_overlap_ratio {f g c : A}
    (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1) (hc : c ∈ 𝒜 1) :
    _root_.HomogeneousLocalization.awayMap 𝒜 hg (rfl : f*g=f*g) (_root_.HomogeneousLocalization.Away.mk 𝒜 hf 1 c (by simpa using hc)) =
      _root_.HomogeneousLocalization.awayMap 𝒜 hf (mul_comm f g) (_root_.HomogeneousLocalization.Away.mk 𝒜 hg 1 c (by simpa using hc)) *
      _root_.HomogeneousLocalization.awayMap 𝒜 hg (rfl : f*g=f*g) (_root_.HomogeneousLocalization.Away.mk 𝒜 hf 1 g (by simpa using hg)) := by
  apply _root_.HomogeneousLocalization.val_injective
  simp only [_root_.HomogeneousLocalization.val_mul, _root_.HomogeneousLocalization.awayMap_mk, _root_.HomogeneousLocalization.Away.val_mk, pow_one,
    Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_one, Submonoid.coe_mul, one_mul]
  ring
end HomogeneousLocalization


/-! Descent of degree-one section ratios along projective basic-open covers. -/
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite _root_.HomogeneousLocalization _root_.OAI.HomogeneousLocalization
namespace ActualSections
open Scheme.Modules
lemma specMap_inv {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (a : A) :
    (Spec.map (CommRingCat.ofHom f)).appTop ((Scheme.ΓSpecIso (.of A)).inv a) =
      (Scheme.ΓSpecIso (.of B)).inv (f a) :=
  ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f)).symm a
lemma ratio_along_eq {X Y : Scheme.{0}} (j k : X ⟶ Y)
    [IsOpenImmersion j] [IsOpenImmersion k] (h : j = k) {M : Y.Modules}
    (s t : SheafOfModules.unit Y.ringCatSheaf ⟶ M) (a : Γ(X,⊤))
    (hr : (restrictUnitIso j).inv ≫ (restrictFunctor j).map s =
      scalar a ≫ (restrictUnitIso j).inv ≫ (restrictFunctor j).map t) :
    (restrictUnitIso k).inv ≫ (restrictFunctor k).map s =
      scalar a ≫ (restrictUnitIso k).inv ≫ (restrictFunctor k).map t := by
  subst k
  exact hr
end ActualSections
namespace AlgebraicGeometry.Proj
open scoped _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Proj
open Scheme.Modules ActualSections
variable {σ A : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]
/-- A homogeneous degree-one quotient. -/
abbrev degreeOneFraction {f c : A} (hf : f ∈ 𝒜 1) (hc : c ∈ 𝒜 1) : Away 𝒜 f :=
  Away.mk 𝒜 hf 1 c (by simpa using hc)
lemma degreeOne_coefficient_identity {f g c : A}
    (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1) (hc : c ∈ 𝒜 1) :
    (degreeOneLeft 𝒜 hf hg).appTop
        ((_root_.AlgebraicGeometry.Scheme.ΓSpecIso (.of (Away 𝒜 f))).inv (degreeOneFraction 𝒜 hf hc)) =
      (degreeOneRight 𝒜 hf hg).appTop
        ((_root_.AlgebraicGeometry.Scheme.ΓSpecIso (.of (Away 𝒜 g))).inv (degreeOneFraction 𝒜 hg hc)) *
      (degreeOneLeft 𝒜 hf hg).appTop
        ((_root_.AlgebraicGeometry.Scheme.ΓSpecIso (.of (Away 𝒜 f))).inv (degreeOneFraction 𝒜 hf hg)) := by
  rw [degreeOneLeft_eq, degreeOneRight_eq, specMap_inv, specMap_inv, specMap_inv, ← map_mul]
  exact congrArg (_root_.AlgebraicGeometry.Scheme.ΓSpecIso (.of (Away 𝒜 (f*g)))).inv
    (degreeOne_overlap_ratio 𝒜 hf hg hc)

lemma degreeOne_section_ratio {I : Type} (f : I → A) (hf : ∀ i, f i ∈ 𝒜 1)
    (hcover : (⨆ i, (_root_.AlgebraicGeometry.Proj.awayι 𝒜 (f i) (hf i) (by decide : 0<1)).opensRange) = ⊤)
    {g c : A} (hg : g ∈ 𝒜 1) (hc : c ∈ 𝒜 1) {M : (_root_.AlgebraicGeometry.Proj 𝒜).Modules}
    (s t : SheafOfModules.unit (_root_.AlgebraicGeometry.Proj 𝒜).ringCatSheaf ⟶ M)
    (u : I → (SheafOfModules.unit (_root_.AlgebraicGeometry.Proj 𝒜).ringCatSheaf ⟶ M))
    (hs : ∀ i, (restrictUnitIso (_root_.AlgebraicGeometry.Proj.awayι 𝒜 (f i) (hf i) (by decide : 0<1))).inv ≫
        (restrictFunctor (_root_.AlgebraicGeometry.Proj.awayι 𝒜 (f i) (hf i) (by decide : 0<1))).map s =
      scalar ((_root_.AlgebraicGeometry.Scheme.ΓSpecIso (.of (Away 𝒜 (f i)))).inv (degreeOneFraction 𝒜 (hf i) hc)) ≫
        (restrictUnitIso (_root_.AlgebraicGeometry.Proj.awayι 𝒜 (f i) (hf i) (by decide : 0<1))).inv ≫
        (restrictFunctor (_root_.AlgebraicGeometry.Proj.awayι 𝒜 (f i) (hf i) (by decide : 0<1))).map (u i))
    (ht : ∀ i, (restrictUnitIso (_root_.AlgebraicGeometry.Proj.awayι 𝒜 (f i) (hf i) (by decide : 0<1))).inv ≫
        (restrictFunctor (_root_.AlgebraicGeometry.Proj.awayι 𝒜 (f i) (hf i) (by decide : 0<1))).map t =
      scalar ((_root_.AlgebraicGeometry.Scheme.ΓSpecIso (.of (Away 𝒜 (f i)))).inv (degreeOneFraction 𝒜 (hf i) hg)) ≫
        (restrictUnitIso (_root_.AlgebraicGeometry.Proj.awayι 𝒜 (f i) (hf i) (by decide : 0<1))).inv ≫
        (restrictFunctor (_root_.AlgebraicGeometry.Proj.awayι 𝒜 (f i) (hf i) (by decide : 0<1))).map (u i)) :
    (restrictUnitIso (_root_.AlgebraicGeometry.Proj.awayι 𝒜 g hg (by decide : 0<1))).inv ≫
        (restrictFunctor (_root_.AlgebraicGeometry.Proj.awayι 𝒜 g hg (by decide : 0<1))).map s =
      scalar ((_root_.AlgebraicGeometry.Scheme.ΓSpecIso (.of (Away 𝒜 g))).inv (degreeOneFraction 𝒜 hg hc)) ≫
        (restrictUnitIso (_root_.AlgebraicGeometry.Proj.awayι 𝒜 g hg (by decide : 0<1))).inv ≫
        (restrictFunctor (_root_.AlgebraicGeometry.Proj.awayι 𝒜 g hg (by decide : 0<1))).map t := by
  apply CoherentGlobal.hom_ext_of_open_charts
    (fun i => _root_.AlgebraicGeometry.Spec (.of (Away 𝒜 (f i * g)))) (fun i => degreeOneRight 𝒜 (hf i) hg)
    (degreeOne_intersection_right_cover 𝒜 hg f hf hcover)
  intro i
  apply restrict_ratio_of_comp
  apply ratio_along_eq _ _ (degreeOne_overlap_square 𝒜 (hf i) hg)
  exact ratio_of_common_frame _ _ _
    (restrict_ratio_comp _ _ s (u i) _ (hs i))
    (restrict_ratio_comp _ _ t (u i) _ (ht i))
    (degreeOne_coefficient_identity 𝒜 (hf i) hg hc)
end AlgebraicGeometry.Proj

end

end OAI
