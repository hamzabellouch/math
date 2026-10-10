import OAI.AlgebraicGeometry.SurfaceCones.CartierFactorization

namespace OAI

private local instance lineSectionModule {Z : AlgebraicGeometry.Scheme.{0}}
    (M : Z.Modules) (U : Z.Opensᵒᵖ) : Module (Z.sheaf.obj.obj U) (M.val.obj U) :=
  (M.val.obj U).isModule

private local instance lineOpenSectionModule {Z : AlgebraicGeometry.Scheme.{0}}
    (M : Z.Modules) (U : Z.Opens) :
    Module (Z.presheaf.obj (Opposite.op U)) (M.val.obj (Opposite.op U)) :=
  (M.val.obj (Opposite.op U)).isModule

private local instance lineCoherentSectionModule {Z : AlgebraicGeometry.Scheme.{0}}
    (M : CoherentGlobal.Coh Z) (U : Z.Opensᵒᵖ) : Module (Z.sheaf.obj.obj U) (M.obj.val.obj U) :=
  (M.obj.val.obj U).isModule

private local instance lineFiniteQuasicoherent {Z : AlgebraicGeometry.Scheme.{0}}
    (M : Z.Modules) [M.IsFinitePresentation] : M.IsQuasicoherent :=
  (SheafOfModules.IsFinitePresentation.exists_quasicoherentData M).choose.isQuasicoherent

/-!
# Conormal lines and generators on completed surface cones

This development accompanies *A Complete Local Domain without a Small
Cohen–Macaulay Module* (OpenAI, 2026).
-/

/-! Epimorphisms between affine trivial line sheaves are isomorphisms. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace ActualAffineLine
open Scheme.Modules CoherentGlobal
variable {R : CommRingCat.{0}} [IsNoetherianRing R]

omit [IsNoetherianRing R] in
lemma gamma_epi {M N : (Spec R).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (φ : M ⟶ N) [Epi φ] : Epi ((moduleSpecΓFunctor (R := R)).map φ) := by
  have hφ : Epi φ := inferInstance
  change SheafOfModules (Spec R).ringCatSheaf at M N
  have hM : IsIso (fromTildeΓ M) := isIso_fromTildeΓ_of_isQuasicoherent M
  have hN : IsIso (fromTildeΓ N) := isIso_fromTildeΓ_of_isQuasicoherent N
  have h := fromTildeΓNatTrans.naturality φ
  have : Epi ((tilde.functor R).map ((moduleSpecΓFunctor (R := R)).map φ) ≫
      fromTildeΓ N) := by
    erw [h]
    change Epi (fromTildeΓ M ≫ φ)
    exact epi_comp' (@IsIso.epi_of_iso _ _ _ _ _ hM) hφ
  have : Epi ((tilde.functor R).map ((moduleSpecΓFunctor (R := R)).map φ)) :=
    (@epi_comp_iff_of_isIso _ _ _ _ _ _ _ hN).mp this
  exact (tilde.functor R).epi_of_epi_map inferInstance

lemma unit_endo_isIso (φ : SheafOfModules.unit (Spec R).ringCatSheaf ⟶
    SheafOfModules.unit (Spec R).ringCatSheaf) [Epi φ] : IsIso φ := by
  have hφ : Epi φ := inferInstance
  let U := SheafOfModules.unit (Spec R).ringCatSheaf
  have : U.IsFinitePresentation := CoherentLocality.finitePresentation_unit _
  have : U.IsQuasicoherent := inferInstance
  have : IsIso (fromTildeΓ U) := isIso_fromTildeΓ_of_isQuasicoherent U
  have : Module.Finite R ((moduleSpecΓFunctor (R := R)).obj U) := finiteGamma_of_coherent U
  have : Epi ((moduleSpecΓFunctor (R := R)).map φ) :=
    @gamma_epi R U U _ _ φ hφ
  have hs := (ModuleCat.epi_iff_surjective ((moduleSpecΓFunctor (R := R)).map φ)).mp this
  have hi := IsNoetherian.injective_of_surjective_endomorphism
    ((moduleSpecΓFunctor (R := R)).map φ).hom hs
  have hΓ : IsIso ((moduleSpecΓFunctor (R := R)).map φ) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr ⟨hi, hs⟩
  have h := fromTildeΓNatTrans.naturality φ
  have : IsIso (fromTildeΓ U ≫ φ) := by
    erw [← h]
    change IsIso ((tilde.functor R).map ((moduleSpecΓFunctor (R := R)).map φ) ≫ fromTildeΓ U)
    exact IsIso.comp_isIso' ((tilde.functor R).mapIso
      (@asIso _ _ _ _ ((moduleSpecΓFunctor (R := R)).map φ) hΓ)).isIso_hom
      (isIso_fromTildeΓ_of_isQuasicoherent U)
  exact IsIso.of_isIso_comp_left (fromTildeΓ U) φ

lemma epi_isIso {M N : (Spec R).Modules} (φ : M ⟶ N) [Epi φ]
    (e : M ≅ SheafOfModules.unit (Spec R).ringCatSheaf)
    (d : N ≅ SheafOfModules.unit (Spec R).ringCatSheaf) : IsIso φ := by
  have hp : Epi (e.inv ≫ φ ≫ d.hom) :=
    epi_comp' (@IsIso.epi_of_iso _ _ _ _ _ e.isIso_inv)
      (epi_comp' inferInstance (@IsIso.epi_of_iso _ _ _ _ _ d.isIso_hom))
  have hc : IsIso (e.inv ≫ φ ≫ d.hom) := @unit_endo_isIso R _ _ hp
  have hc' : IsIso (φ ≫ d.hom) :=
    @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ e.isIso_inv hc
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ d.isIso_hom hc'
end ActualAffineLine

end

/-! The pullback of the plane-divisor ideal is the exceptional ideal,
and their conormal lines agree under the finite surface map. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace SourcePullbackChart
open KummerSourceModel SourceConeMorphism SourceZeroSections Scheme.Modules ActualCartier
  ActualSheafTensor ActualSheafBaseChange
attribute [local instance] integralSurfaceCommRing integralSurfaceSemiring
  integralPullbackCommRing integralPullbackSemiring pullbackBaseAlgebra surfaceOriginAlgebra
  completedPullbackModule completedPullbackAction completedPullbackSMul completedPullbackTower
  completedSurfaceModule completedSeriesModule completedSourceChartCommRing completedSourceChartSemiring
  completedSourceAlgebra
  originChartCommRing originChartSemiring originPlaneCommRing originPlaneSemiring
  chartBaseAlgebra planeOriginAlgebra baseChartModule baseChartAction baseChartSMul baseChartTower
  planeOriginModule completedBlowupCommRing completedBlowupSemiring completedBlowupAlgebra

/-- The composite of base change with the pullback unit isomorphism. -/
def closedStructureBaseChangeIso :
    (Scheme.Modules.pullback g).obj ((pushforward completedPlaneZero).obj
      (SheafOfModules.unit ExplicitCone.plane.ringCatSheaf)) ≅
    (pushforward completedSourceZero).obj (SheafOfModules.unit ExplicitCone.projectiveSurface.ringCatSheaf) := by
  have : (SheafOfModules.unit ExplicitCone.plane.ringCatSheaf).IsFinitePresentation :=
    CoherentLocality.finitePresentation_unit _
  have := swappedActualMate_isIso (SheafOfModules.unit ExplicitCone.plane.ringCatSheaf)
  exact asIso ((mate completedPlaneZero g ExplicitCone.projectiveNormalization completedSourceZero
      completedSourceZero_g.symm).app (SheafOfModules.unit _)) ≪≫
    (pushforward completedSourceZero).mapIso (sheafPullbackUnitIso ExplicitCone.projectiveNormalization)

lemma closedStructureBaseChange_comm :
    (Scheme.Modules.pullback g).map (structureMap completedPlaneZero) ≫
      closedStructureBaseChangeIso.hom =
    (sheafPullbackUnitIso g).hom ≫ structureMap completedSourceZero :=
  baseChange_structure completedPlaneZero g ExplicitCone.projectiveNormalization completedSourceZero
    completedSourceZero_g.symm

/-- The canonical morphism from the pulled-back ideal to the ideal. -/
def idealBaseChange : (Scheme.Modules.pullback g).obj (idealSheaf completedPlaneZero) ⟶
    idealSheaf completedSourceZero :=
  ActualRightExactIdeal.comparison (Scheme.Modules.pullback g) (structureMap completedPlaneZero)
    (structureMap completedSourceZero) (sheafPullbackUnitIso g) closedStructureBaseChangeIso
    closedStructureBaseChange_comm

instance idealBaseChange_epi : Epi idealBaseChange := by
  have hE : Epi (structureMap completedPlaneZero) := structureMap_epi _ planeIdealLine
  exact @ActualRightExactIdeal.comparison_epi _ _ _ _ _ _ (Scheme.Modules.pullback g)
    _ _ _ _ (structureMap completedPlaneZero) hE _ _ (structureMap completedSourceZero)
    (sheafPullbackUnitIso g) closedStructureBaseChangeIso closedStructureBaseChange_comm

lemma idealBaseChange_ι : idealBaseChange ≫ idealι completedSourceZero =
    (Scheme.Modules.pullback g).map (idealι completedPlaneZero) ≫ (sheafPullbackUnitIso g).hom :=
  ActualRightExactIdeal.comparison_ι _ _ _ _ _ _

/-- Pulled-back plane ideal, on the completed source chart. -/
def pulledPlaneIdealChartIso (i : Fin 3) :
    (restrictFunctor (completedIota i)).obj
      ((Scheme.Modules.pullback g).obj (idealSheaf completedPlaneZero)) ≅
    SheafOfModules.unit (Spec (.of (completedSourceChart i))).ringCatSheaf :=
  (restrictFunctorIsoPullback (completedIota i)).app _ ≪≫
    (pullbackComp (completedIota i) g).app _ ≪≫
    (pullbackCongr (completedIota_projection i)).app _ ≪≫
    ((pullbackComp (completedProjection i) (completedBlowupIota i)).app _).symm ≪≫
    (Scheme.Modules.pullback (completedProjection i)).mapIso
      (((restrictFunctorIsoPullback (completedBlowupIota i)).app _).symm ≪≫
        planeIdealChartIso i) ≪≫ sheafPullbackUnitIso (completedProjection i)

lemma idealBaseChange_chart_isIso (i : Fin 3) :
    IsIso ((restrictFunctor (completedIota i)).map idealBaseChange) :=
  ActualAffineLine.epi_isIso _ (pulledPlaneIdealChartIso i) (sourceIdealChartIso i)

instance idealBaseChange_isIso : IsIso idealBaseChange := by
  apply CoherentGlobal.isIso_of_open_cover (fun i : Fin 3 => (completedIota i).opensRange)
    completedCover.iSup_opensRange idealBaseChange
  intro i
  have := idealBaseChange_chart_isIso i
  let e := (restrictFunctorComp (completedIota i).isoOpensRange.inv (completedIota i)).symm ≪≫
    restrictFunctorCongr (Scheme.Hom.isoOpensRange_inv_comp (completedIota i))
  have hx : IsIso (((restrictFunctor (completedIota i)) ⋙
      restrictFunctor (completedIota i).isoOpensRange.inv).map idealBaseChange) := by
    change IsIso ((restrictFunctor (completedIota i).isoOpensRange.inv).map
      ((restrictFunctor (completedIota i)).map idealBaseChange))
    infer_instance
  exact ((NatIso.isIso_map_iff e idealBaseChange)).mp hx

def idealBaseChangeIso : (Scheme.Modules.pullback g).obj (idealSheaf completedPlaneZero) ≅
    idealSheaf completedSourceZero := asIso idealBaseChange

/-- The conormal identity i*J ≅ f*(z*I) for the two kernel ideals. -/
def conormalBaseChangeIso :
    (Scheme.Modules.pullback completedSourceZero).obj (idealSheaf completedSourceZero) ≅
    (Scheme.Modules.pullback ExplicitCone.projectiveNormalization).obj
      ((Scheme.Modules.pullback completedPlaneZero).obj (idealSheaf completedPlaneZero)) :=
  (Scheme.Modules.pullback completedSourceZero).mapIso idealBaseChangeIso.symm ≪≫
    (pullbackComp completedSourceZero g).app _ ≪≫
    (pullbackCongr completedSourceZero_g).app _ ≪≫
    ((pullbackComp ExplicitCone.projectiveNormalization completedPlaneZero).app _).symm
end SourcePullbackChart

end

/-! Morphisms from the structure sheaf are determined by global sections. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualSections
open Scheme.Modules
variable {X : Scheme.{0}}

def restrictTop (M : X.Modules) (s : M.val.obj (op ⊤)) (U : X.Opens) : M.val.obj (op U) :=
  M.val.map (homOfLE (show U ≤ ⊤ from le_top)).op s

def family (M : X.Modules) (s : M.val.obj (op ⊤)) : M.sections :=
  M.val.sectionsMk (fun U => M.val.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op s) (by
    intro U V f
    rw [← PresheafOfModules.map_comp_apply]
    congr 1)

def fromUnit (M : X.Modules) (s : M.val.obj (op ⊤)) : SheafOfModules.unit _ ⟶ M :=
  M.unitHomEquiv.symm (family M s)

lemma fromUnit_app (M : X.Modules) (s : M.val.obj (op ⊤)) (U : X.Opens) (r : Γ(X,U)) :
    (fromUnit M s).val.app (op U) r =
      r • restrictTop M s U := by
  rfl

lemma fromUnit_top (M : X.Modules) (s : M.val.obj (op ⊤)) (r : Γ(X,⊤)) :
    (fromUnit M s).val.app (op ⊤) r = r • s := by
  rw [fromUnit_app]
  congr 1
  dsimp only [restrictTop]
  have he : (homOfLE (show (⊤ : X.Opens) ≤ ⊤ from le_top)).op = 𝟙 (op ⊤) := Subsingleton.elim _ _
  rw [he]
  rw [PresheafOfModules.map_id]
  rfl

lemma fromUnit_comp {M N : X.Modules} (s : M.val.obj (op ⊤)) (φ : M ⟶ N) :
    fromUnit M s ≫ φ = fromUnit N (φ.val.app (op ⊤) s) := by
  erw [fromUnit, SheafOfModules.unitHomEquiv_symm_comp]
  apply congrArg N.unitHomEquiv.symm
  apply Subtype.ext
  funext U
  exact (PresheafOfModules.naturality_apply φ.val
    (homOfLE (show U.unop ≤ ⊤ from le_top)).op s)

abbrev scalar (r : Γ(X,⊤)) : SheafOfModules.unit X.ringCatSheaf ⟶
    SheafOfModules.unit X.ringCatSheaf := fromUnit _ r
end ActualSections

namespace ActualCartier
open Scheme.Modules ActualSections
variable {X Y : Scheme.{0}} (f : X ⟶ Y)

def idealGlobalSection (r : Γ(Y,⊤)) (hr : f.app ⊤ r = 0) :
    (idealSheaf f).val.obj (op ⊤) :=
  (sectionKernelEquiv f ⊤).symm.toFun ⟨r, hr⟩

lemma idealGlobalSection_ι (r : Γ(Y,⊤)) (hr : f.app ⊤ r = 0) :
    (idealι f).val.app (op ⊤) (idealGlobalSection f r hr) = r := by
  have h := (sectionKernelEquiv f ⊤).apply_symm_apply ⟨r, hr⟩
  exact congrArg Subtype.val h

def idealGenerator (r : Γ(Y,⊤)) (hr : f.app ⊤ r = 0) :
    SheafOfModules.unit Y.ringCatSheaf ⟶ idealSheaf f :=
  fromUnit _ (idealGlobalSection f r hr)

lemma idealGenerator_ι (r : Γ(Y,⊤)) (hr : f.app ⊤ r = 0) :
    idealGenerator f r hr ≫ idealι f = scalar r := by
  erw [idealGenerator, fromUnit_comp, idealGlobalSection_ι]
end ActualCartier

end

/-! An affine quasicoherent morphism is invertible when its map on global sections is bijective. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualAffineLine
open Scheme.Modules CoherentGlobal
variable {R : CommRingCat.{0}} {M N : (Spec R).Modules}
  [M.IsQuasicoherent] [N.IsQuasicoherent]

lemma isIso_of_top_bijective (φ : M ⟶ N)
    (hb : Function.Bijective (φ.val.app (op ⊤))) : IsIso φ := by
  have hi : IsIso ((moduleSpecΓFunctor (R := R)).map φ) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hb
  obtain ⟨ψ, hψ⟩ := affineGamma_surjective N M (inv ((moduleSpecΓFunctor (R := R)).map φ))
  dsimp only at hψ
  refine ⟨⟨ψ, ?_, ?_⟩⟩
  · apply affineGamma_injective
    dsimp only
    erw [Functor.map_comp, hψ, CategoryTheory.Functor.map_id, IsIso.hom_inv_id]
  · apply affineGamma_injective
    dsimp only
    erw [Functor.map_comp, hψ, CategoryTheory.Functor.map_id, IsIso.inv_hom_id]
end ActualAffineLine

end

/-! A global Cartier equation generates the ideal on every affine chart
where it is a regular generator of the kernel. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualSections
open Scheme.Modules
variable {X Y : Scheme.{0}} (j : X ⟶ Y) [IsOpenImmersion j]

lemma restrictScalar_top (r : Γ(Y,⊤)) (a : Γ(X,⊤)) :
    (((restrictUnitIso j).inv ≫ (restrictFunctor j).map (scalar r) ≫
      (restrictUnitIso j).hom).val.app (op ⊤)) a = j.appTop r * a := by
  change (j.appIso ⊤).hom ((j.appIso ⊤).inv a *
    Y.presheaf.map (homOfLE (show j ''ᵁ ⊤ ≤ ⊤ from le_top)).op r) = _
  rw [map_mul, Iso.inv_hom_id_apply]
  rw [mul_comm]
  congr 1
  have hh : Y.presheaf.map (homOfLE (show j ''ᵁ ⊤ ≤ ⊤ from le_top)).op ≫
      (j.appIso ⊤).hom = j.appTop := by
    rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]
    erw [Scheme.Hom.appLE_eq_app]
  exact ConcreteCategory.congr_hom hh r
end ActualSections

namespace ActualCartier
open Scheme.Modules ActualSections
variable {X Y X' : Scheme.{0}} {A : CommRingCat.{0}}
  (f : X ⟶ Y) (g : X' ⟶ Spec A) (k : X' ⟶ X) (j : Spec A ⟶ Y)
  [IsOpenImmersion k] [IsOpenImmersion j]
  (hw : k ≫ f = g ≫ j) (hp : k ''ᵁ ⊤ = f ⁻¹ᵁ (j ''ᵁ ⊤))

def chartGenerator (r : Γ(Y,⊤)) (hr : f.app ⊤ r = 0) :
    SheafOfModules.unit (Spec A).ringCatSheaf ⟶ (restrictFunctor j).obj (idealSheaf f) :=
  (restrictUnitIso j).inv ≫ (restrictFunctor j).map (idealGenerator f r hr)

lemma chartGenerator_section (r : Γ(Y,⊤)) (hr : f.app ⊤ r = 0) (a : Γ(Spec A,⊤)) :
    (chartIdealSectionMap f j).toFun ((chartGenerator f j r hr).val.app (op ⊤) a) =
      j.appTop r * a := by
  have he : chartGenerator f j r hr ≫ (restrictFunctor j).map (idealι f) ≫
      (restrictUnitIso j).hom =
      (restrictUnitIso j).inv ≫ (restrictFunctor j).map (scalar r) ≫
        (restrictUnitIso j).hom := by
    dsimp only [chartGenerator]
    erw [Category.assoc, ← Functor.map_comp_assoc, idealGenerator_ι]
    rfl
  have h := congrArg (fun φ => φ.val.app (op ⊤) a) he
  exact h.trans (restrictScalar_top j r a)

include hw hp in
lemma chartGenerator_isIso [((restrictFunctor j).obj (idealSheaf f)).IsQuasicoherent]
    (r : Γ(Y,⊤)) (hr : f.app ⊤ r = 0)
    (ht : IsSMulRegular Γ(Spec A,⊤) (j.appTop r))
    (hker : RingHom.ker g.appTop.hom = Ideal.span {j.appTop r}) :
    IsIso (chartGenerator f j r hr) := by
  let e := chartIdealSectionsEquiv f g k j hw hp
  let p := principalIdealEquiv _ (j.appTop r) ht hker
  have he : ∀ a : Γ(Spec A,⊤),
      e.toFun ((chartGenerator f j r hr).val.app (op ⊤) a) = p.symm a := by
    intro a
    apply Subtype.ext
    exact chartGenerator_section f j r hr a
  have : (SheafOfModules.unit (Spec A).ringCatSheaf).IsFinitePresentation :=
    CoherentLocality.finitePresentation_unit _
  apply ActualAffineLine.isIso_of_top_bijective
  have hh : (fun a : Γ(Spec A,⊤) =>
      e.toFun ((chartGenerator f j r hr).val.app (op ⊤) a)) = p.symm := funext he
  apply (e.bijective.of_comp_iff' _).mp
  change Function.Bijective (fun a => e.toFun ((chartGenerator f j r hr).val.app (op ⊤) a))
  erw [hh]
  exact p.symm.bijective
end ActualCartier

end

/-! The three original parameters generate the plane exceptional ideal.
Each parameter trivializes it on the corresponding completed standard chart. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite TensorProduct
namespace SourcePullbackChart
open KummerSourceModel SourceZeroSections Scheme.Modules ActualCartier ActualSections
attribute [local instance] originChartCommRing originChartSemiring originPlaneCommRing originPlaneSemiring
  chartBaseAlgebra planeOriginAlgebra baseChartModule baseChartAction baseChartSMul baseChartTower
  planeOriginModule completedBlowupCommRing completedBlowupSemiring completedBlowupAlgebra

lemma completedBlowupFiber_eq_right (i : Fin 3) :
    completedBlowupFiber i = (1 : chart i) ⊗ₜ[S] (MvPowerSeries.X i : A) := by
  have h := Algebra.TensorProduct.tmul_one_eq_one_tmul (R := S) (A := chart i) (B := A)
    (MvPolynomial.X i)
  change completedBlowupFiber i = 1 ⊗ₜ[S] MvPolynomial.toMvPowerSeries (MvPolynomial.X i) at h
  simpa only [MvPolynomial.coe_X] using h

def planeParameter (i : Fin 3) : Γ(V,⊤) :=
  completedBlowdown.appTop ((Scheme.ΓSpecIso (.of A)).inv (MvPowerSeries.X i))

lemma planeParameter_killed (i : Fin 3) : completedPlaneZero.app ⊤ (planeParameter i) = 0 := by
  change (completedBlowdown.appTop ≫ completedPlaneZero.appTop)
    ((Scheme.ΓSpecIso (.of A)).inv (MvPowerSeries.X i)) = 0
  rw [← Scheme.Hom.comp_appTop, completedPlaneZero_blowdown, Scheme.Hom.comp_appTop]
  change planeScalar.appTop (seriesOrigin.appTop
    ((Scheme.ΓSpecIso (.of A)).inv (MvPowerSeries.X i))) = 0
  have he := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (MvPowerSeries.constantCoeff : A →+* ℂ))).symm (MvPowerSeries.X i)
  change seriesOrigin.appTop ((Scheme.ΓSpecIso (.of A)).inv (MvPowerSeries.X i)) = _ at he
  rw [he]
  change planeScalar.appTop ((Scheme.ΓSpecIso (.of ℂ)).inv
    (MvPowerSeries.constantCoeff (MvPowerSeries.X i : A))) = 0
  rw [MvPowerSeries.constantCoeff_X, map_zero, map_zero]

lemma planeParameter_chart (i : Fin 3) :
    (completedBlowupIota i).appTop (planeParameter i) =
      (Scheme.ΓSpecIso (.of (completedBlowupChart i))).inv (completedBlowupFiber i) := by
  change (completedBlowdown.appTop ≫ (completedBlowupIota i).appTop)
    ((Scheme.ΓSpecIso (.of A)).inv (MvPowerSeries.X i)) = _
  rw [← Scheme.Hom.comp_appTop, completedBlowupIota_second]
  have he := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : A →+* completedBlowupChart i))).symm
      (MvPowerSeries.X i)
  change (baseChartSecond i).appTop ((Scheme.ΓSpecIso (.of A)).inv (MvPowerSeries.X i)) = _ at he
  exact he.trans (congrArg (Scheme.ΓSpecIso (.of (completedBlowupChart i))).inv
    (completedBlowupFiber_eq_right i).symm)

def planeIdealGenerator (i : Fin 3) : SheafOfModules.unit V.ringCatSheaf ⟶
    idealSheaf completedPlaneZero :=
  idealGenerator completedPlaneZero (planeParameter i) (planeParameter_killed i)

lemma planeIdealGenerator_chart_isIso (i : Fin 3) :
    IsIso ((restrictFunctor (completedBlowupIota i)).map (planeIdealGenerator i)) := by
  have : (idealSheaf completedPlaneZero).IsFinitePresentation := idealSheaf_coherent _
  have : ((restrictFunctor (completedBlowupIota i)).obj (idealSheaf completedPlaneZero)).IsFinitePresentation :=
    CoherentGlobal.coherent_restrict _ _
  have hi := chartGenerator_isIso completedPlaneZero
    (Spec.map (CommRingCat.ofHom (completedPlaneEvaluation i)))
    (planeIota i) (completedBlowupIota i) (planeIota_completedPlaneZero i)
    (by simpa only [Scheme.Hom.image_top_eq_opensRange] using (planeZero_chart_preimage i).symm)
    (planeParameter i) (planeParameter_killed i)
    (by rw [planeParameter_chart]; exact specInverse_regular _ (completedBlowupFiber_regular i))
    (by rw [planeParameter_chart]; exact specMap_app_kernel _ _ (completedPlaneEvaluation_kernel i))
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _
    (restrictUnitIso (completedBlowupIota i)).isIso_inv hi
end SourcePullbackChart

end

/-! Epimorphisms of module sheaves descend from open immersion charts. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace CoherentGlobal
open Scheme.Modules
variable {Y : Scheme.{0}} {I : Type} (X : I → Scheme.{0}) (j : ∀ i, X i ⟶ Y)
  [∀ i, IsOpenImmersion (j i)] (hc : (⨆ i, (j i).opensRange) = ⊤)

include hc

lemma hom_ext_of_open_charts {M N : Y.Modules} {a b : M ⟶ N}
    (h : ∀ i, (restrictFunctor (j i)).map a = (restrictFunctor (j i)).map b) : a = b := by
  apply hom_ext_of_open_cover (fun i => (j i).opensRange) hc
  intro i
  let e := (restrictFunctorComp (j i).isoOpensRange.inv (j i)).symm ≪≫
    restrictFunctorCongr (Scheme.Hom.isoOpensRange_inv_comp (j i))
  apply (cancel_epi (e.hom.app M)).mp
  rw [← e.hom.naturality, ← e.hom.naturality]
  change (restrictFunctor (j i).isoOpensRange.inv).map ((restrictFunctor (j i)).map a) ≫ _ = _
  rw [h i]
  rfl

lemma epi_of_open_charts {M N : Y.Modules} (φ : M ⟶ N)
    (h : ∀ i, Epi ((restrictFunctor (j i)).map φ)) : Epi φ := by
  constructor
  intro P a b hab
  apply hom_ext_of_open_charts X j hc
  intro i
  have := h i
  apply (cancel_epi ((restrictFunctor (j i)).map φ)).mp
  simpa only [Functor.map_comp] using congrArg ((restrictFunctor (j i)).map) hab
end CoherentGlobal

end

/-! Three-generator presentations of the exceptional ideals and conormal lines
using the original parameters. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace SourcePullbackChart
open KummerSourceModel SourceZeroSections Scheme.Modules ActualCartier ActualSheafTensor
attribute [local instance] originChartCommRing originChartSemiring originPlaneCommRing originPlaneSemiring
  chartBaseAlgebra planeOriginAlgebra baseChartModule baseChartAction baseChartSMul baseChartTower
  planeOriginModule completedBlowupCommRing completedBlowupSemiring completedBlowupAlgebra

def planeIdealPresentation : SheafOfModules.free (R := V.ringCatSheaf) (Fin 3) ⟶
    idealSheaf completedPlaneZero := Sigma.desc planeIdealGenerator

@[reassoc] lemma planeIdealPresentation_generator (i : Fin 3) :
    SheafOfModules.ιFree i ≫ planeIdealPresentation = planeIdealGenerator i :=
  Sigma.ι_comp_desc _ _

instance planeIdealPresentation_epi : Epi planeIdealPresentation := by
  apply CoherentGlobal.epi_of_open_charts (fun i => Spec (.of (completedBlowupChart i)))
    completedBlowupIota completedBlowupCover
  intro i
  let F := restrictFunctor (completedBlowupIota i)
  have he : F.map (SheafOfModules.ιFree i) ≫ F.map planeIdealPresentation =
      F.map (planeIdealGenerator i) := by
    exact (F.map_comp _ _).symm.trans (congrArg F.map (planeIdealPresentation_generator i))
  have : IsIso (F.map (planeIdealGenerator i)) := planeIdealGenerator_chart_isIso i
  have : Epi (F.map (SheafOfModules.ιFree i) ≫ F.map planeIdealPresentation) := by
    rw [he]
    infer_instance
  exact epi_of_epi (F.map (SheafOfModules.ιFree i)) (F.map planeIdealPresentation)

def pullbackFreeIso {X Y : Scheme.{0}} (f : X ⟶ Y) (I : Type) :
    SheafOfModules.free (R := X.ringCatSheaf) I ≅
      (Scheme.Modules.pullback f).obj (SheafOfModules.free (R := Y.ringCatSheaf) I) := by
  let F : SheafOfModules Y.ringCatSheaf ⥤ SheafOfModules X.ringCatSheaf := Scheme.Modules.pullback f
  have : F.IsLeftAdjoint := inferInstanceAs (Scheme.Modules.pullback f).IsLeftAdjoint
  exact SheafOfModules.mapFreeIso F I (sheafPullbackUnitIso f).symm

def planeConormalPresentation :
    SheafOfModules.free (R := ExplicitCone.plane.ringCatSheaf) (Fin 3) ⟶
      (Scheme.Modules.pullback completedPlaneZero).obj (idealSheaf completedPlaneZero) :=
  (pullbackFreeIso completedPlaneZero (Fin 3)).hom ≫
      (Scheme.Modules.pullback completedPlaneZero).map planeIdealPresentation

instance planeConormalPresentation_epi : Epi planeConormalPresentation := by
  let F : SheafOfModules V.ringCatSheaf ⥤ SheafOfModules ExplicitCone.plane.ringCatSheaf :=
    Scheme.Modules.pullback completedPlaneZero
  have : F.IsLeftAdjoint := inferInstanceAs (Scheme.Modules.pullback completedPlaneZero).IsLeftAdjoint
  have hm : Epi (F.map planeIdealPresentation) :=
    @Functor.map_epi _ _ _ _ F _ _ _ planeIdealPresentation planeIdealPresentation_epi
  change Epi ((pullbackFreeIso completedPlaneZero (Fin 3)).hom ≫ F.map planeIdealPresentation)
  exact epi_comp' (@IsIso.epi_of_iso _ _ _ _ _
    (pullbackFreeIso completedPlaneZero (Fin 3)).isIso_hom) hm

def sourceConormalPresentation :
    SheafOfModules.free (R := ExplicitCone.projectiveSurface.ringCatSheaf) (Fin 3) ⟶
      (Scheme.Modules.pullback completedSourceZero).obj (idealSheaf completedSourceZero) :=
  (pullbackFreeIso ExplicitCone.projectiveNormalization (Fin 3)).hom ≫
      (Scheme.Modules.pullback ExplicitCone.projectiveNormalization).map planeConormalPresentation ≫
        conormalBaseChangeIso.inv

instance sourceConormalPresentation_epi : Epi sourceConormalPresentation := by
  let F : SheafOfModules ExplicitCone.plane.ringCatSheaf ⥤
      SheafOfModules ExplicitCone.projectiveSurface.ringCatSheaf :=
    Scheme.Modules.pullback ExplicitCone.projectiveNormalization
  have : F.IsLeftAdjoint := inferInstanceAs
    (Scheme.Modules.pullback ExplicitCone.projectiveNormalization).IsLeftAdjoint
  have hm : Epi (F.map planeConormalPresentation) :=
    @Functor.map_epi _ _ _ _ F _ _ _ planeConormalPresentation planeConormalPresentation_epi
  change Epi ((pullbackFreeIso ExplicitCone.projectiveNormalization (Fin 3)).hom ≫
    F.map planeConormalPresentation ≫ conormalBaseChangeIso.inv)
  exact epi_comp' (@IsIso.epi_of_iso _ _ _ _ _
    (pullbackFreeIso ExplicitCone.projectiveNormalization (Fin 3)).isIso_hom)
    (epi_comp' hm (@IsIso.epi_of_iso _ _ _ _ _ conormalBaseChangeIso.isIso_inv))

/-- Global generation by three global sections on the source
surface. The target is the conormal to its completed zero section. -/
theorem sourceConormal_generated : ∃ (φ :
    SheafOfModules.free (R := ExplicitCone.projectiveSurface.ringCatSheaf) (Fin 3) ⟶
      (Scheme.Modules.pullback completedSourceZero).obj (idealSheaf completedSourceZero)), Epi φ :=
  ⟨sourceConormalPresentation, inferInstance⟩
end SourcePullbackChart

end

/-! Pullback comparison across a commuting open-chart square. -/
noncomputable section
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace ActualChartPullback
open Scheme.Modules
variable {A B C D : Scheme.{0}}
  (j : C ⟶ A) (f : A ⟶ B) (q : C ⟶ D) (k : D ⟶ B)
  [IsOpenImmersion j] [IsOpenImmersion k] (h : j ≫ f = q ≫ k)

def squareIso : Scheme.Modules.pullback f ⋙ restrictFunctor j ≅
    restrictFunctor k ⋙ Scheme.Modules.pullback q :=
  Functor.isoWhiskerLeft (Scheme.Modules.pullback f) (restrictFunctorIsoPullback j) ≪≫
    pullbackComp j f ≪≫ pullbackCongr h ≪≫ (pullbackComp q k).symm ≪≫
      Functor.isoWhiskerRight (restrictFunctorIsoPullback k).symm (Scheme.Modules.pullback q)

include h in
lemma map_isIso {M N : B.Modules} (φ : M ⟶ N)
    [IsIso ((restrictFunctor k).map φ)] :
    IsIso ((restrictFunctor j).map ((Scheme.Modules.pullback f).map φ)) := by
  have : IsIso ((restrictFunctor k ⋙ Scheme.Modules.pullback q).map φ) := by
    change IsIso ((Scheme.Modules.pullback q).map ((restrictFunctor k).map φ))
    infer_instance
  exact (NatIso.isIso_map_iff (squareIso j f q k h) φ).mpr this
end ActualChartPullback

end

/-! Rank additivity on affine charts preserves the source rank under elementary modifications. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Scheme.Modules
namespace CoherentChartRank
lemma module_add {R : Type} [CommRing R] [IsDomain R]
    (S : ShortComplex (ModuleCat.{0} R)) (hS : S.ShortExact)
    [Module.Finite R S.X₂] :
    Module.finrank R S.X₂ = Module.finrank R S.X₁ + Module.finrank R S.X₃ := by
  have hf : Function.Injective S.f := (ModuleCat.mono_iff_injective _).mp hS.mono_f
  have hg : Function.Surjective S.g := (ModuleCat.epi_iff_surjective _).mp hS.epi_g
  have h := (LinearMap.ker S.g.hom).finrank_quotient_add_finrank
  rw [(S.g.hom.quotKerEquivOfSurjective hg).finrank_eq,
    ← S.moduleCat_exact_iff_range_eq_ker.mp hS.exact,
    ← (LinearEquiv.ofInjective S.f.hom hf).finrank_eq] at h
  exact h.symm.trans (Nat.add_comm _ _)

lemma affineGamma_shortExact {R : CommRingCat.{0}} (S : ShortComplex (Spec R).Modules)
    [IsIso (fromTildeΓ S.X₁)] [IsIso (fromTildeΓ S.X₂)] [IsIso (fromTildeΓ S.X₃)]
    (hS : S.ShortExact) : (S.map (moduleSpecΓFunctor (R := R))).ShortExact := by
  have ht := ShortComplex.shortExact_of_iso (CoherentGlobal.shortComplexTildeIso S).symm hS
  have hf : Mono (S.map (moduleSpecΓFunctor (R := R))).f := by
    have : Mono ((tilde.functor R).map ((S.map moduleSpecΓFunctor).f)) := ht.mono_f
    exact (tilde.functor R).mono_of_mono_map inferInstance
  have hg : Epi (S.map (moduleSpecΓFunctor (R := R))).g := by
    have : Epi ((tilde.functor R).map ((S.map moduleSpecΓFunctor).g)) := ht.epi_g
    exact (tilde.functor R).epi_of_epi_map inferInstance
  exact { exact := (CoherentGlobal.exact_iff_affineGamma S).mp hS.exact }

open CoherentGlobal
abbrev chartSections {X : Scheme.{0}} {R : CommRingCat.{0}}
    (j : Spec R ⟶ X) [IsOpenImmersion j] (B : Coh X) : ModuleCat R :=
  (moduleSpecΓFunctor (R := R)).obj ((restrictFunctor j).obj B.obj)

lemma chartSections_finite {X : Scheme.{0}} {R : CommRingCat.{0}}
    [IsNoetherianRing R] (j : Spec R ⟶ X) [IsOpenImmersion j] (B : Coh X) :
    Module.Finite R (chartSections j B) := by
  have := B.property
  have := coherent_restrict j B.obj
  exact finiteGamma_of_coherent _

lemma chart_add {X : Scheme.{0}} [IsLocallyNoetherian X] {R : CommRingCat.{0}}
    [IsNoetherianRing R] [IsDomain R] (j : Spec R ⟶ X) [IsOpenImmersion j]
    (S : ShortComplex (Coh X)) (hS : S.ShortExact) :
    Module.finrank R (chartSections j S.X₂) =
      Module.finrank R (chartSections j S.X₁) + Module.finrank R (chartSections j S.X₃) := by
  let T := (S.map (cohInclusion X)).map (restrictFunctor j)
  have := S.X₁.property
  have := S.X₂.property
  have := S.X₃.property
  have : T.X₁.IsFinitePresentation := coherent_restrict j S.X₁.obj
  have : T.X₂.IsFinitePresentation := coherent_restrict j S.X₂.obj
  have : T.X₃.IsFinitePresentation := coherent_restrict j S.X₃.obj
  have : IsIso (fromTildeΓ T.X₁) := isIso_fromTildeΓ_of_isQuasicoherent _
  have : IsIso (fromTildeΓ T.X₂) := isIso_fromTildeΓ_of_isQuasicoherent _
  have : IsIso (fromTildeΓ T.X₃) := isIso_fromTildeΓ_of_isQuasicoherent _
  have ht : T.ShortExact := (hS.map_of_exact (cohInclusion X)).map_of_exact (restrictFunctor j)
  have : Module.Finite R (T.map moduleSpecΓFunctor).X₂ := chartSections_finite j S.X₂
  exact module_add _ (affineGamma_shortExact T ht)
end CoherentChartRank

end

/-! The conormal twist has rank one on the source charts,
so elementary modifications preserve the generic rank. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Scheme.Modules
namespace SourceConeMorphism
open KummerSourceModel SourcePullbackChart SourceZeroSections CoherentGlobal ActualCartier
  ActualSheafTensor
attribute [local instance] integralSurfaceCommRing integralSurfaceSemiring
  integralPullbackCommRing integralPullbackSemiring pullbackBaseAlgebra surfaceOriginAlgebra
  completedPullbackModule completedPullbackAction completedPullbackSMul completedPullbackTower
  completedSurfaceModule completedSeriesModule completedSourceChartCommRing completedSourceChartSemiring
  completedSourceAlgebra

local instance sourceChart_noetherian (i : Fin 3) : IsNoetherianRing (surfaceChart i) :=
  isNoetherianRing_of_surjective (completedSourceChart i) (surfaceChart i)
    (completedZeroEvaluation i) (completedZeroEvaluation_surjective i)

abbrev surfaceChartRank (B : Coh ExplicitCone.projectiveSurface) (i : Fin 3) : ℕ :=
  Module.finrank (surfaceChart i) (CoherentChartRank.chartSections (surfaceIota i) B)

def conormalChartUnitIso (i : Fin 3) :
    (restrictFunctor (surfaceIota i)).obj
      ((Scheme.Modules.pullback completedSourceZero).obj (idealSheaf completedSourceZero)) ≅
        SheafOfModules.unit (Spec (.of (surfaceChart i))).ringCatSheaf :=
  SourceExceptionalRestriction.chartPullbackIso _ i ≪≫
    (Scheme.Modules.pullback (completedZeroChart i)).mapIso (sourceIdealChartIso i) ≪≫
    sheafPullbackUnitIso (completedZeroChart i)

def conormalChartIso (G : Coh ExplicitCone.projectiveSurface) (i : Fin 3) :
    (restrictFunctor (surfaceIota i)).obj
      (conormalTensor completedSourceZero sourceIdealLine G).obj ≅
      (restrictFunctor (surfaceIota i)).obj G.obj :=
  (tensorOpenRestrictNatIso (surfaceIota i)
    ((Scheme.Modules.pullback completedSourceZero).obj (idealSheaf completedSourceZero))).app G.obj ≪≫
    (trivialTensorIso (Spec (.of (surfaceChart i))).sheaf (conormalChartUnitIso i)).app _

lemma conormal_rank (G : Coh ExplicitCone.projectiveSurface) (i : Fin 3) :
    surfaceChartRank (conormalTensor completedSourceZero sourceIdealLine G) i =
      surfaceChartRank G i :=
  ((moduleSpecΓFunctor (R := CommRingCat.of (surfaceChart i))).mapIso
    (conormalChartIso G i)).toLinearEquiv.finrank_eq

lemma elementaryTransform_rank {B : Coh W} {G : Coh ExplicitCone.projectiveSurface}
    (q : sourceRestriction.obj B ⟶ G) [Epi q]
    (hB : ∀ U, Module.IsTorsionFree (W.sheaf.obj.obj U) (B.obj.val.obj U)) (i : Fin 3) :
    surfaceChartRank (sourceRestriction.obj (elementaryTransform q)) i =
      surfaceChartRank (sourceRestriction.obj B) i := by
  let S : ShortComplex (Coh ExplicitCone.projectiveSurface) :=
    ShortComplex.mk (kernel.ι q) q (kernel.condition q)
  have hs : S.ShortExact := { exact := ShortComplex.exact_kernel q }
  have h₀ := CoherentChartRank.chart_add (surfaceIota i) S hs
  have h₁ := CoherentChartRank.chart_add (surfaceIota i)
    (transformSequence completedSourceZero sourceIdealLine q)
    (transformSequence_shortExact completedSourceZero sourceIdealLine q hB)
  change surfaceChartRank (sourceRestriction.obj B) i =
    surfaceChartRank (kernel q) i + surfaceChartRank G i at h₀
  change surfaceChartRank (sourceRestriction.obj (elementaryTransform q)) i =
    surfaceChartRank (conormalTensor completedSourceZero sourceIdealLine G) i +
      surfaceChartRank (kernel q) i at h₁
  rw [conormal_rank] at h₁
  exact h₁.trans ((Nat.add_comm _ _).trans h₀.symm)

lemma initial_restriction_rank (M : ModuleCat.{0} ExplicitCone.completedRing)
    [Module.Finite ExplicitCone.completedRing M] (i : Fin 3) :
    surfaceChartRank (sourceRestriction.obj (coherentModel M)) i =
      Module.finrank ExplicitCone.completedRing M := by
  let e := (moduleSpecΓFunctor (R := CommRingCat.of (surfaceChart i))).mapIso
    ((restrictFunctor (surfaceIota i)).mapIso (sourceRestrictionIso (coherentModel M)).symm)
  exact e.toLinearEquiv.finrank_eq.trans (SourceExceptionalRestriction.chart_rank_eq M i)
end SourceConeMorphism

end

/-! The three source conormal generators are induced by the parameters.
The ith section is a frame on the ith source projective chart. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace SourcePullbackChart
open KummerSourceModel SourceZeroSections Scheme.Modules ActualCartier ActualSheafTensor
attribute [local instance] integralSurfaceCommRing integralSurfaceSemiring
  integralPullbackCommRing integralPullbackSemiring pullbackBaseAlgebra surfaceOriginAlgebra
  completedPullbackModule completedPullbackAction completedPullbackSMul completedPullbackTower
  completedSurfaceModule completedSeriesModule completedSourceChartCommRing completedSourceChartSemiring
  completedSourceAlgebra
  originChartCommRing originChartSemiring originPlaneCommRing originPlaneSemiring
  chartBaseAlgebra planeOriginAlgebra baseChartModule baseChartAction baseChartSMul baseChartTower
  planeOriginModule completedBlowupCommRing completedBlowupSemiring completedBlowupAlgebra

def sourceIdealGenerator (i : Fin 3) : SheafOfModules.unit W.ringCatSheaf ⟶
    idealSheaf completedSourceZero :=
  (sheafPullbackUnitIso g).inv ≫ (Scheme.Modules.pullback g).map (planeIdealGenerator i) ≫
    idealBaseChangeIso.hom

lemma sourceIdealGenerator_chart_isIso (i : Fin 3) :
    IsIso ((restrictFunctor (completedIota i)).map (sourceIdealGenerator i)) := by
  have : IsIso ((restrictFunctor (completedBlowupIota i)).map (planeIdealGenerator i)) :=
    planeIdealGenerator_chart_isIso i
  have hm := ActualChartPullback.map_isIso (completedIota i) g (completedProjection i)
    (completedBlowupIota i) (completedIota_projection i) (planeIdealGenerator i)
  dsimp only [sourceIdealGenerator]
  erw [Functor.map_comp, Functor.map_comp]
  exact IsIso.comp_isIso'
    (((restrictFunctor (completedIota i)).mapIso (sheafPullbackUnitIso g).symm).isIso_hom)
    (IsIso.comp_isIso' hm
      (((restrictFunctor (completedIota i)).mapIso idealBaseChangeIso).isIso_hom))

def sourceConormalGenerator (i : Fin 3) :
    SheafOfModules.unit ExplicitCone.projectiveSurface.ringCatSheaf ⟶
      (Scheme.Modules.pullback completedSourceZero).obj (idealSheaf completedSourceZero) :=
  (sheafPullbackUnitIso completedSourceZero).inv ≫
    (Scheme.Modules.pullback completedSourceZero).map (sourceIdealGenerator i)

lemma sourceConormalGenerator_chart_isIso (i : Fin 3) :
    IsIso ((restrictFunctor (surfaceIota i)).map (sourceConormalGenerator i)) := by
  have : IsIso ((restrictFunctor (completedIota i)).map (sourceIdealGenerator i)) :=
    sourceIdealGenerator_chart_isIso i
  have hm := ActualChartPullback.map_isIso (surfaceIota i) completedSourceZero (completedZeroChart i)
    (completedIota i) (surfaceIota_completedSourceZero i) (sourceIdealGenerator i)
  dsimp only [sourceConormalGenerator]
  erw [Functor.map_comp]
  exact IsIso.comp_isIso'
    (((restrictFunctor (surfaceIota i)).mapIso (sheafPullbackUnitIso completedSourceZero).symm).isIso_hom) hm

/-- Line trivializations induced by these global sections. -/
def sourceConormalFrame (i : Fin 3) :
    (restrictFunctor (surfaceIota i)).obj
      ((Scheme.Modules.pullback completedSourceZero).obj (idealSheaf completedSourceZero)) ≅
        SheafOfModules.unit (Spec (.of (surfaceChart i))).ringCatSheaf := by
  have := sourceConormalGenerator_chart_isIso i
  exact (asIso ((restrictFunctor (surfaceIota i)).map (sourceConormalGenerator i))).symm ≪≫
    restrictUnitIso (surfaceIota i)

def sourceConormalLine : ActualSheafTensor.LineTrivialization ExplicitCone.projectiveSurface.sheaf
    ((Scheme.Modules.pullback completedSourceZero).obj (idealSheaf completedSourceZero)) :=
  lineTrivializationOfCharts _ (fun i => Spec (.of (surfaceChart i))) surfaceIota surfaceIota_cover
    sourceConormalFrame
end SourcePullbackChart

end

/-! Cartier generators have the transition ratios determined by their ideal inclusions. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualSections
open Scheme.Modules
variable {X : Scheme.{0}} {M : X.Modules}

lemma unitHom_ext_top {φ ψ : SheafOfModules.unit X.ringCatSheaf ⟶ M}
    (h : φ.val.app (op ⊤) (1 : Γ(X,⊤)) = ψ.val.app (op ⊤) (1 : Γ(X,⊤))) : φ = ψ := by
  apply M.unitHomEquiv.injective
  apply Subtype.ext
  funext U
  change φ.val.app U (1 : Γ(X,U.unop)) = ψ.val.app U (1 : Γ(X,U.unop))
  have hφ := PresheafOfModules.naturality_apply φ.val
    (homOfLE (show U.unop ≤ ⊤ from le_top)).op (1 : Γ(X,⊤))
  have hψ := PresheafOfModules.naturality_apply ψ.val
    (homOfLE (show U.unop ≤ ⊤ from le_top)).op (1 : Γ(X,⊤))
  change φ.val.app U (X.presheaf.map _ 1) =
    M.val.map _ (φ.val.app (op ⊤) (1 : Γ(X,⊤))) at hφ
  change ψ.val.app U (X.presheaf.map _ 1) =
    M.val.map _ (ψ.val.app (op ⊤) (1 : Γ(X,⊤))) at hψ
  rw [map_one] at hφ hψ
  rw [hφ, hψ, h]
end ActualSections
namespace ActualCartier
open Scheme.Modules ActualSections
variable {X Y : Scheme.{0}} {A : CommRingCat.{0}}
  (f : X ⟶ Y) (j : Spec A ⟶ Y) [IsOpenImmersion j]

lemma chartGenerator_ratio (r s : Γ(Y,⊤))
    (hr : f.app ⊤ r = 0) (hs : f.app ⊤ s = 0)
    (a : Γ(Spec A,⊤)) (he : j.appTop s = a * j.appTop r) :
    chartGenerator f j s hs = scalar a ≫ chartGenerator f j r hr := by
  apply unitHom_ext_top
  apply chartIdealSectionMap_injective f j
  change (chartIdealSectionMap f j).toFun
      ((chartGenerator f j s hs).val.app (op ⊤) (1 : Γ(Spec A,⊤))) =
    (chartIdealSectionMap f j).toFun
      ((chartGenerator f j r hr).val.app (op ⊤) ((scalar a).val.app (op ⊤) (1 : Γ(Spec A,⊤))))
  erw [chartGenerator_section, fromUnit_top, one_smul, chartGenerator_section, he]
  ring
end ActualCartier

end

/-! The global plane exceptional-ideal sections have standard projective
transition ratios, with residue x_j/x_i on the zero section. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite TensorProduct
namespace SourcePullbackChart
open KummerSourceModel SourceZeroSections Scheme.Modules ActualCartier ActualSections
attribute [local instance] originChartCommRing originChartSemiring originPlaneCommRing originPlaneSemiring
  chartBaseAlgebra planeOriginAlgebra baseChartModule baseChartAction baseChartSMul baseChartTower
  planeOriginModule completedBlowupCommRing completedBlowupSemiring completedBlowupAlgebra

/-- The pullback of the projective coordinate x_j/x_i to V_i. -/
def planeTransitionCoefficient (i j : Fin 3) : completedBlowupChart i :=
  directionMap i (SectionCompletion.polynomialChartDehom i (MvPolynomial.X j)) ⊗ₜ[S] 1

lemma planeTransitionCoefficient_mul_fiber (i j : Fin 3) :
    planeTransitionCoefficient i j * completedBlowupFiber i =
      (1 : chart i) ⊗ₜ[S] (MvPowerSeries.X j : A) := by
  rw [planeTransitionCoefficient, completedBlowupFiber, Algebra.TensorProduct.tmul_mul_tmul,
    one_mul, ratio_relation]
  have h := Algebra.TensorProduct.tmul_one_eq_one_tmul (R := S) (A := chart i) (B := A)
    (MvPolynomial.X j)
  change baseMap i (MvPolynomial.X j) ⊗ₜ[S] (1 : A) =
    1 ⊗ₜ[S] MvPolynomial.toMvPowerSeries (MvPolynomial.X j) at h
  simpa only [MvPolynomial.coe_X] using h

lemma planeParameter_on_chart (i j : Fin 3) :
    (completedBlowupIota i).appTop (planeParameter j) =
      (Scheme.ΓSpecIso (.of (completedBlowupChart i))).inv
        ((1 : chart i) ⊗ₜ[S] (MvPowerSeries.X j : A)) := by
  change (completedBlowdown.appTop ≫ (completedBlowupIota i).appTop)
    ((Scheme.ΓSpecIso (.of A)).inv (MvPowerSeries.X j)) = _
  rw [← Scheme.Hom.comp_appTop, completedBlowupIota_second]
  exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : A →+* completedBlowupChart i))).symm
      (MvPowerSeries.X j)

lemma planeParameter_chart_ratio (i j : Fin 3) :
    (completedBlowupIota i).appTop (planeParameter j) =
      (Scheme.ΓSpecIso (.of (completedBlowupChart i))).inv (planeTransitionCoefficient i j) *
        (completedBlowupIota i).appTop (planeParameter i) := by
  rw [planeParameter_on_chart, planeParameter_chart, ← map_mul,
    planeTransitionCoefficient_mul_fiber]

lemma planeIdealGenerator_chart_ratio (i j : Fin 3) :
    (restrictUnitIso (completedBlowupIota i)).inv ≫
      (restrictFunctor (completedBlowupIota i)).map (planeIdealGenerator j) =
    scalar ((Scheme.ΓSpecIso (.of (completedBlowupChart i))).inv
      (planeTransitionCoefficient i j)) ≫
      (restrictUnitIso (completedBlowupIota i)).inv ≫
        (restrictFunctor (completedBlowupIota i)).map (planeIdealGenerator i) :=
  chartGenerator_ratio completedPlaneZero (completedBlowupIota i)
    (planeParameter i) (planeParameter j) (planeParameter_killed i) (planeParameter_killed j)
    _ (planeParameter_chart_ratio i j)

lemma planeTransitionCoefficient_residue (i j : Fin 3) :
    completedPlaneEvaluation i (planeTransitionCoefficient i j) =
      SectionCompletion.polynomialChartDehom i (MvPolynomial.X j) := by
  rw [planeTransitionCoefficient, completedPlaneEvaluation_tmul,
    map_one, map_one, mul_one]
  change zeroEvaluation i (directionMap i _) = _
  rw [← planePolynomialEquiv_C]
  change Polynomial.eval 0 ((planePolynomialEquiv i).symm ((planePolynomialEquiv i) _)) = _
  rw [AlgEquiv.symm_apply_apply, Polynomial.eval_C]
end SourcePullbackChart

end

end OAI
