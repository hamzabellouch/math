import Mathlib
import OAI.CategoryTheory.Thomason.FiniteGluing

namespace OAI

/-! Core Couniversality. -/

noncomputable section
universe u v w z


namespace Thomason
open CategoryTheory Limits DirectedComplex NormalizedChains OmegaCategory

namespace RelativePrismData
variable {E : Type u} [PartialOrder E] {A : Set E} (d : RelativePrismData E A)
variable (T : RightIntervalCore.{u})
variable {P Q : Type u} [LinearOrder P] [LinearOrder Q] [Finite P] [Finite Q]

def corePrismLeg (σ : P →o E) :
    T.tensor.obj (categorification.obj (nerve P)) ⟶ categorification.obj (nerve E) :=
  T.tensor.map (posetCategorificationTableMap P) ≫ (T.simplex P) ≫
    (d.finiteCylinderChainMap σ).nu ≫ (d.finiteImage σ).lift

lemma corePrismLeg_natural (σ : Q →o E) (α : P →o Q) :
    T.tensor.map (categorification.map (nerveMap α.monotone.functor)) ≫ d.corePrismLeg T σ =
      d.corePrismLeg T (σ.comp α) := by
  unfold corePrismLeg
  rw [← Category.assoc, ← T.tensor.map_comp, posetCategorificationTableMap_natural,
    T.tensor.map_comp, Category.assoc, ← Category.assoc (T.tensor.map (complexMap α).nu),
    T.simplex_natural, Category.assoc]
  have hc := congrArg Hom.nu (d.finiteCylinderChainMap_natural σ α)
  change (show (complex P).cylinder.nu ⟶ _ from (d.finiteCylinderChainMap (σ.comp α)).nu) ≫
      (complexMap ((d.finiteImage (σ.comp α)).subInclusion (d.finiteImage σ)
        (d.finiteImage_mono σ α))).nu =
      (complexMap α).cylinder.nu ≫ (d.finiteCylinderChainMap σ).nu at hc
  have hcc := congrArg (fun z : (complex P).cylinder.nu ⟶ (complex (d.finiteImage σ).vertices).nu =>
    T.tensor.map (posetCategorificationTableMap P) ≫ (T.simplex P) ≫ z ≫
      (d.finiteImage σ).lift) hc
  simp only [Category.assoc, FiniteVertexChain.lift_natural] at hcc
  exact hcc.symm

lemma corePrismLeg_endpoint_false (σ : P →o E) :
    (T.endpoint false).app (categorification.obj (nerve P)) ≫ d.corePrismLeg T σ =
      categorification.map (nerveMap (d.f.comp σ).monotone.functor) := by
  unfold corePrismLeg
  rw [← Category.assoc, ← (T.endpoint false).naturality, Category.assoc,
    ← Category.assoc ((T.endpoint false).app (complex P).nu), T.simplex_endpoint, CategoryTheory.Functor.id_map]
  have hc := congrArg Hom.nu (d.finiteAntihomotopy σ).cylinderHom_endpoint_false
  change (show (complex P).nu ⟶ (complex P).cylinder.nu from ((complex P).cylinderEndpoint false).nu) ≫ (d.finiteCylinderChainMap σ).nu =
    (complexMap (d.finiteImageLeft σ)).nu at hc
  have hcc := congrArg (fun z : (complex P).nu ⟶ (complex (d.finiteImage σ).vertices).nu =>
    posetCategorificationTableMap P ≫ z ≫ (d.finiteImage σ).lift) hc
  simp only [Category.assoc] at hcc
  exact hcc.trans ((d.finiteImage σ).map_lift (d.finiteImageLeft σ))

lemma corePrismLeg_endpoint_true (σ : P →o E) :
    (T.endpoint true).app (categorification.obj (nerve P)) ≫ d.corePrismLeg T σ =
      categorification.map (nerveMap (d.g.comp σ).monotone.functor) := by
  unfold corePrismLeg
  rw [← Category.assoc, ← (T.endpoint true).naturality, Category.assoc,
    ← Category.assoc ((T.endpoint true).app (complex P).nu), T.simplex_endpoint, CategoryTheory.Functor.id_map]
  have hc := congrArg Hom.nu (d.finiteAntihomotopy σ).cylinderHom_endpoint_true
  change (show (complex P).nu ⟶ (complex P).cylinder.nu from ((complex P).cylinderEndpoint true).nu) ≫ (d.finiteCylinderChainMap σ).nu =
    (complexMap (d.finiteImageRight σ)).nu at hc
  have hcc := congrArg (fun z : (complex P).nu ⟶ (complex (d.finiteImage σ).vertices).nu =>
    posetCategorificationTableMap P ≫ z ≫ (d.finiteImage σ).lift) hc
  simp only [Category.assoc] at hcc
  exact hcc.trans ((d.finiteImage σ).map_lift (d.finiteImageRight σ))

lemma corePrismLeg_stationary (σ : P →o E) (hs : ∀ p, σ p ∈ A) :
    d.corePrismLeg T σ = T.projection.app (categorification.obj (nerve P)) ≫
      categorification.map (nerveMap (d.f.comp σ).monotone.functor) := by
  unfold corePrismLeg
  rw [d.finiteCylinderChainMap_stationary σ hs]
  change T.tensor.map (posetCategorificationTableMap P) ≫ (T.simplex P) ≫
    (complex P).cylinderProjection.nu ≫ (complexMap (d.finiteImageLeft σ)).nu ≫
      (d.finiteImage σ).lift = _
  rw [← Category.assoc (T.simplex P), T.simplex_projection,
    ← Category.assoc (T.tensor.map (posetCategorificationTableMap P)),
    T.projection.naturality, Category.assoc, CategoryTheory.Functor.id_map, FiniteVertexChain.map_lift]
  rfl

def corePrismCocone : Cocone (posetSimplexDiagram E ⋙ T.tensor) where
  pt := categorification.obj (nerve E)
  ι.app s := d.corePrismLeg T (simplexVertexOrder s)
  ι.naturality s t α := by
    change T.tensor.map (categorification.map (nerveMap (simplexVertexMap α).monotone.functor)) ≫
      d.corePrismLeg T (simplexVertexOrder t) = d.corePrismLeg T (simplexVertexOrder s) ≫ 𝟙 _
    rw [d.corePrismLeg_natural, simplexVertexOrder_natural, Category.comp_id]

def corePrism : T.tensor.obj (categorification.obj (nerve E)) ⟶ categorification.obj (nerve E) := by
  letI := T.cocontinuous
  letI : PreservesColimitsOfSize.{0,u} T.tensor := preservesColimitsOfSize_shrink T.tensor
  exact (isColimitOfPreserves T.tensor (posetSimplexIsColimit E)).desc (d.corePrismCocone T)

lemma corePrism_leg (s : SimplexIndex E) :
    T.tensor.map (categorification.map (nerveMap (simplexVertexOrder s).monotone.functor)) ≫
       d.corePrism T = d.corePrismLeg T (simplexVertexOrder s) := by
  let := T.cocontinuous
  let : PreservesColimitsOfSize.{0,u} T.tensor := preservesColimitsOfSize_shrink T.tensor
  exact (isColimitOfPreserves T.tensor (posetSimplexIsColimit E)).fac (d.corePrismCocone T) s

lemma corePrism_endpoint_false :
    (T.endpoint false).app (categorification.obj (nerve E)) ≫ d.corePrism T =
      categorification.map (nerveMap d.f.monotone.functor) := by
  apply (posetSimplexIsColimit E).hom_ext
  intro s
  change categorification.map (nerveMap (simplexVertexOrder s).monotone.functor) ≫
    (T.endpoint false).app (categorification.obj (nerve E)) ≫ d.corePrism T =
      categorification.map (nerveMap (simplexVertexOrder s).monotone.functor) ≫
        categorification.map (nerveMap d.f.monotone.functor)
  have hn := (T.endpoint false).naturality
    (categorification.map (nerveMap (simplexVertexOrder s).monotone.functor))
  simp only [CategoryTheory.Functor.id_map] at hn
  rw [← Category.assoc, hn, Category.assoc,
    d.corePrism_leg, d.corePrismLeg_endpoint_false]
  rw [← categorification.map_comp]
  congr 1

lemma corePrism_endpoint_true :
    (T.endpoint true).app (categorification.obj (nerve E)) ≫ d.corePrism T =
      categorification.map (nerveMap d.g.monotone.functor) := by
  apply (posetSimplexIsColimit E).hom_ext
  intro s
  change categorification.map (nerveMap (simplexVertexOrder s).monotone.functor) ≫
    (T.endpoint true).app (categorification.obj (nerve E)) ≫ d.corePrism T =
      categorification.map (nerveMap (simplexVertexOrder s).monotone.functor) ≫
        categorification.map (nerveMap d.g.monotone.functor)
  have hn := (T.endpoint true).naturality
    (categorification.map (nerveMap (simplexVertexOrder s).monotone.functor))
  simp only [CategoryTheory.Functor.id_map] at hn
  rw [← Category.assoc, hn, Category.assoc,
    d.corePrism_leg, d.corePrismLeg_endpoint_true]
  rw [← categorification.map_comp]
  congr 1

end RelativePrismData
end Thomason

end

noncomputable section
universe u v w z


namespace Thomason
open CategoryTheory Limits DirectedComplex NormalizedChains OmegaCategory

namespace RelativePrismData
variable {E : Type u} [PartialOrder E] {A : Set E} (d : RelativePrismData E A)
variable (T : RightIntervalCore.{u})

lemma coreGrayPrism_stationary {P : Type u} [PartialOrder P] (v : P →o E) (hv : ∀ p, v p ∈ A) :
    T.tensor.map (categorification.map (nerveMap v.monotone.functor)) ≫ d.corePrism T =
      T.projection.app (categorification.obj (nerve P)) ≫
        categorification.map (nerveMap (d.f.comp v).monotone.functor) := by
  let := T.cocontinuous
  let : PreservesColimitsOfSize.{0,u} T.tensor := preservesColimitsOfSize_shrink T.tensor
  apply (isColimitOfPreserves T.tensor (posetSimplexIsColimit P)).hom_ext
  intro s
  change T.tensor.map (categorification.map (nerveMap (simplexVertexOrder s).monotone.functor)) ≫
      T.tensor.map (categorification.map (nerveMap v.monotone.functor)) ≫ d.corePrism T =
    T.tensor.map (categorification.map (nerveMap (simplexVertexOrder s).monotone.functor)) ≫
      T.projection.app (categorification.obj (nerve P)) ≫
        categorification.map (nerveMap (d.f.comp v).monotone.functor)
  rw [← Category.assoc, ← T.tensor.map_comp, ← categorification.map_comp]
  have hvn : nerveMap (simplexVertexOrder s).monotone.functor ≫ nerveMap v.monotone.functor =
      nerveMap (simplexVertexOrder (s.postcompose v)).monotone.functor := by
    rw [simplexVertexOrder_postcompose]
    rfl
  erw [hvn, d.corePrism_leg T (s.postcompose v), d.corePrismLeg_stationary T _ (fun p => hv _),
    ← Category.assoc, T.projection.naturality, CategoryTheory.Functor.id_map,
    Category.assoc, ← categorification.map_comp]
  congr 1

lemma coreGrayPrism_stationary_inclusion :
    T.tensor.map (categorification.map (nerveMap (OrderHom.Subtype.val (fun element : E => element ∈ A)).monotone.functor)) ≫
      d.corePrism T = T.projection.app (categorification.obj (nerve A)) ≫
        categorification.map (nerveMap (d.f.comp (OrderHom.Subtype.val (fun element : E => element ∈ A))).monotone.functor) :=
  d.coreGrayPrism_stationary T (OrderHom.Subtype.val (fun element : E => element ∈ A)) (fun p => p.property)

end RelativePrismData
end Thomason

end

noncomputable section
universe u v w z


namespace Thomason
open CategoryTheory Limits OmegaCategory

namespace RelativePrismData
variable {E : Type u} [PartialOrder E] {A : Set E} (d : RelativePrismData E A)
variable (T : RightIntervalCore.{u}) (R : OmegaCategory.{u} ⥤ OmegaCategory.{u})
variable (adj : T.tensor ⊣ R) (n : ℕ)

def coreFinitePrism :
    T.tensor.obj ((categorificationFinite n).obj (nerve E)).val ⟶
      ((categorificationFinite n).obj (nerve E)).val :=
  (T.truncatedCylinderEquiv R adj n (categorification.obj (nerve E))
    ((categorificationFinite n).obj (nerve E)).val
    ((categorificationFinite n).obj (nerve E)).property).symm
      (d.corePrism T ≫ truncationUnit n (categorification.obj (nerve E)))

lemma coreFinitePrism_unit :
    T.tensor.map (truncationUnit n (categorification.obj (nerve E))) ≫
      d.coreFinitePrism T R adj n = d.corePrism T ≫ truncationUnit n (categorification.obj (nerve E)) := by
  erw [← T.truncatedCylinderEquiv_apply R adj n _ _
    ((categorificationFinite n).obj (nerve E)).property]
  exact Equiv.apply_symm_apply _ _

lemma coreFinitePrism_endpoint_false :
    (T.endpoint false).app ((categorificationFinite n).obj (nerve E)).val ≫
      d.coreFinitePrism T R adj n = (categorificationFinite n).map (nerveMap d.f.monotone.functor) := by
  apply truncation_functor_ext (n := n)
  have hn := (T.endpoint false).naturality
    (truncationUnit n (categorification.obj (nerve E)))
  exact (congrArg (fun h : categorification.obj (nerve E) ⟶
      T.tensor.obj ((categorificationFinite n).obj (nerve E)).val =>
    h ≫ d.coreFinitePrism T R adj n) hn).trans
      ((congrArg (fun h => (T.endpoint false).app (categorification.obj (nerve E)) ≫ h)
        (d.coreFinitePrism_unit T R adj n)).trans
        (congrArg (fun h : categorification.obj (nerve E) ⟶ categorification.obj (nerve E) =>
          h ≫ truncationUnit n (categorification.obj (nerve E)))
          (d.corePrism_endpoint_false T)))

lemma coreFinitePrism_endpoint_true :
    (T.endpoint true).app ((categorificationFinite n).obj (nerve E)).val ≫
      d.coreFinitePrism T R adj n = (categorificationFinite n).map (nerveMap d.g.monotone.functor) := by
  apply truncation_functor_ext (n := n)
  have hn := (T.endpoint true).naturality
    (truncationUnit n (categorification.obj (nerve E)))
  exact (congrArg (fun h : categorification.obj (nerve E) ⟶
      T.tensor.obj ((categorificationFinite n).obj (nerve E)).val =>
    h ≫ d.coreFinitePrism T R adj n) hn).trans
      ((congrArg (fun h => (T.endpoint true).app (categorification.obj (nerve E)) ≫ h)
        (d.coreFinitePrism_unit T R adj n)).trans
        (congrArg (fun h : categorification.obj (nerve E) ⟶ categorification.obj (nerve E) =>
          h ≫ truncationUnit n (categorification.obj (nerve E)))
          (d.corePrism_endpoint_true T)))

lemma coreFinitePrism_stationary {P : Type u} [PartialOrder P] (v : P →o E) (hv : ∀ p, v p ∈ A) :
    T.tensor.map ((categorificationFinite n).map (nerveMap v.monotone.functor)) ≫
      d.coreFinitePrism T R adj n =
      T.projection.app ((categorificationFinite n).obj (nerve P)).val ≫
        (categorificationFinite n).map (nerveMap (d.f.comp v).monotone.functor) := by
  apply (T.truncatedCylinderEquiv R adj n (categorification.obj (nerve P))
    ((categorificationFinite n).obj (nerve E)).val
    ((categorificationFinite n).obj (nerve E)).property).injective
  erw [T.truncatedCylinderEquiv_apply, T.truncatedCylinderEquiv_apply]
  erw [← Category.assoc, ← T.tensor.map_comp]
  have hn : truncationUnit n (categorification.obj (nerve P)) ≫
      (show ((categorificationFinite n).obj (nerve P)).val ⟶
          ((categorificationFinite n).obj (nerve E)).val from
      (categorificationFinite n).map (nerveMap v.monotone.functor)) =
      categorification.map (nerveMap v.monotone.functor) ≫
        truncationUnit n (categorification.obj (nerve E)) := rfl
  erw [hn, T.tensor.map_comp, Category.assoc, d.coreFinitePrism_unit,
    ← Category.assoc, d.coreGrayPrism_stationary T v hv,
    Category.assoc]
  exact congrArg (fun h : T.tensor.obj (categorification.obj (nerve P)) ⟶
      ((categorificationFinite n).obj (nerve P)).val =>
    h ≫ (categorificationFinite n).map (nerveMap (d.f.comp v).monotone.functor))
      (T.projection.naturality (truncationUnit n (categorification.obj (nerve P)))).symm

end RelativePrismData
end Thomason

end

noncomputable section
universe u v w z


namespace Thomason.RightIntervalCore
open CategoryTheory Simplicial MonoidalCategory Opposite
open DirectedComplex NormalizedChains OmegaCategory
open RightIntervalExtension (raiseSimplex up_raiseSimplex raiseSimplex_precomp up_simplexMap)

def SimplexDescent (T : RightIntervalCore.{u}) (d : ℕ) : Prop :=
  ∀ (P : Type u) [LinearOrder P] [Finite P] (Y : OmegaCategory.{u}), Y.IsTruncated d →
    Function.Bijective (fun G : (complex P).cylinder.nu ⟶ Y => T.simplex P ≫ G)

lemma intervalCore_simplexDescent_two :
    GrayRecursive.IntervalHom.intervalCore.SimplexDescent 2 :=
  GrayRecursive.IntervalHom.chainComparison_precomp_bijective_two

variable (T : RightIntervalCore.{u}) {d : ℕ} (S : T.SimplexDescent d)

def simplexLift {P : Type u} [LinearOrder P] [Finite P] {Y : OmegaCategory.{u}}
    (hY : Y.IsTruncated d) (F : T.tensor.obj (complex P).nu ⟶ Y) :
    (complex P).cylinder.nu ⟶ Y :=
  (Equiv.ofBijective (fun G : (complex P).cylinder.nu ⟶ Y => T.simplex P ≫ G)
    (S P Y hY)).symm F

lemma simplexLift_fac {P : Type u} [LinearOrder P] [Finite P] {Y : OmegaCategory.{u}}
    (hY : Y.IsTruncated d) (F : T.tensor.obj (complex P).nu ⟶ Y) :
    T.simplex P ≫ T.simplexLift S hY F = F := by
  exact (Equiv.ofBijective (fun G : (complex P).cylinder.nu ⟶ Y => T.simplex P ≫ G)
    (S P Y hY)).apply_symm_apply F

lemma simplexLift_natural {P Q : Type u} [LinearOrder P] [Finite P]
    [LinearOrder Q] [Finite Q] {Y : OmegaCategory.{u}} (hY : Y.IsTruncated d)
    (f : Hom (complex P) (complex Q)) (F : T.tensor.obj (complex Q).nu ⟶ Y) :
    f.cylinder.nu ≫ T.simplexLift S hY F =
      T.simplexLift S hY (T.tensor.map f.nu ≫ F) := by
  apply (S P Y hY).1
  change T.simplex P ≫ (f.cylinder.nu ≫ T.simplexLift S hY F) =
    T.simplex P ≫ T.simplexLift S hY (T.tensor.map f.nu ≫ F)
  rw [T.simplexLift_fac, ← Category.assoc, ← T.simplex_natural,
    Category.assoc, T.simplexLift_fac]

lemma simplexLift_endpoint {P : Type u} [LinearOrder P] [Finite P]
    {Y : OmegaCategory.{u}} (hY : Y.IsTruncated d)
    (F : T.tensor.obj (complex P).nu ⟶ Y) (ε : Bool) :
    ((complex P).cylinderEndpoint ε).nu ≫ T.simplexLift S hY F =
      (T.endpoint ε).app (complex P).nu ≫ F := by
  rw [← T.simplex_endpoint, Category.assoc, T.simplexLift_fac]

def cutApply {P : Type u} [LinearOrder P] [Finite P] {Y : OmegaCategory.{u}}
    (hY : Y.IsTruncated d) (F : T.tensor.obj (complex P).nu ⟶ Y) (θ : P →o Fin 2) :
    (complex P).nu ⟶ Y := (awHom θ).nu ≫ T.simplexLift S hY F

lemma cutApply_natural {P Q : Type u} [LinearOrder P] [Finite P]
    [LinearOrder Q] [Finite Q] {Y : OmegaCategory.{u}} (hY : Y.IsTruncated d)
    (f : P →o Q) (F : T.tensor.obj (complex Q).nu ⟶ Y) (θ : Q →o Fin 2) :
    (complexMap f).nu ≫ T.cutApply S hY F θ =
      T.cutApply S hY (T.tensor.map (complexMap f).nu ≫ F) (θ.comp f) := by
  unfold cutApply
  change (Hom.comp (complexMap f) (awHom θ)).nu ≫ T.simplexLift S hY F = _
  rw [awHom_naturality]
  change (awHom (θ.comp f)).nu ≫ ((complexMap f).cylinder.nu ≫ T.simplexLift S hY F) = _
  rw [T.simplexLift_natural]

lemma cutApply_endpoint {P : Type u} [LinearOrder P] [Finite P]
    {Y : OmegaCategory.{u}} (hY : Y.IsTruncated d)
    (F : T.tensor.obj (complex P).nu ⟶ Y) (ε : Bool) :
    T.cutApply S hY F (OrderHom.const P (if ε then 1 else 0)) =
      (T.endpoint ε).app (complex P).nu ≫ F := by
  unfold cutApply
  rw [awHom_endpoint, T.simplexLift_endpoint]

def nerveCylinderSimplex {X Y : OmegaCategory.{u}} (hY : Y.IsTruncated d)
    (P : T.tensor.obj X ⟶ Y) (m : ℕ) (F : OmegaCategory.Functor (Oriental m) X)
    (θ : Fin (m+1) →o Fin 2) : OmegaCategory.Functor (Oriental m) Y :=
  OmegaCategory.Functor.comp (complexMap (orderULiftUp.{0,u} (Fin (m+1)))).nu
    (T.cutApply S hY (T.tensor.map (raiseSimplex F) ≫ P) (θ.comp (orderULiftDown _)))

lemma nerveCylinderSimplex_natural {X Y : OmegaCategory.{u}} (hY : Y.IsTruncated d)
    (P : T.tensor.obj X ⟶ Y) {m n : ℕ} (a : Fin (m+1) →o Fin (n+1))
    (F : OmegaCategory.Functor (Oriental n) X) (θ : Fin (n+1) →o Fin 2) :
    T.nerveCylinderSimplex S hY P m (OmegaCategory.Functor.comp (complexMap a).nu F)
      (θ.comp a) = OmegaCategory.Functor.comp (complexMap a).nu
        (T.nerveCylinderSimplex S hY P n F θ) := by
  unfold nerveCylinderSimplex
  rw [raiseSimplex_precomp, T.tensor.map_comp, Category.assoc]
  let b := (orderULiftUp.{0,u} (Fin (n+1))).comp (a.comp (orderULiftDown _))
  have hc : (θ.comp a).comp (orderULiftDown _) =
      (θ.comp (orderULiftDown _)).comp b := rfl
  rw [hc, ← T.cutApply_natural]
  exact congrArg (fun f => OmegaCategory.Functor.comp f
    (T.cutApply S hY (T.tensor.map (raiseSimplex F) ≫ P) (θ.comp (orderULiftDown _))))
      (up_simplexMap a)

lemma nerveCylinderSimplex_endpoint {X Y : OmegaCategory.{u}} (hY : Y.IsTruncated d)
    (P : T.tensor.obj X ⟶ Y) (m : ℕ) (F : OmegaCategory.Functor (Oriental m) X) (ε : Bool) :
    T.nerveCylinderSimplex S hY P m F (OrderHom.const _ (if ε then 1 else 0)) =
      OmegaCategory.Functor.comp F ((T.endpoint ε).app X ≫ P) := by
  unfold nerveCylinderSimplex
  have hc : (OrderHom.const (Fin (m+1)) (if ε then (1 : Fin 2) else 0)).comp
      (orderULiftDown.{0,u} (Fin (m+1))) = OrderHom.const _ (if ε then 1 else 0) := rfl
  rw [hc, T.cutApply_endpoint]
  have hn := (T.endpoint ε).naturality (raiseSimplex F)
  exact (congrArg (fun f => OmegaCategory.Functor.comp
    (complexMap (orderULiftUp.{0,u} (Fin (m+1)))).nu (f ≫ P)) hn.symm).trans
    (congrArg (fun f => OmegaCategory.Functor.comp f ((T.endpoint ε).app X ≫ P))
      (up_raiseSimplex F))

def nerveCylinder {X Y : OmegaCategory.{u}} (hY : Y.IsTruncated d) (P : T.tensor.obj X ⟶ Y) :
    streetNerve X ⊗ Δ[1] ⟶ streetNerve Y where
  app m := ↾fun x => T.nerveCylinderSimplex S hY P m.unop.len x.1
    (SSet.stdSimplex.objEquiv x.2).toOrderHom
  naturality m n a := by
    apply ConcreteCategory.hom_ext
    intro x
    exact T.nerveCylinderSimplex_natural S hY P a.unop.toOrderHom x.1
      (SSet.stdSimplex.objEquiv x.2).toOrderHom

lemma nerveCylinder_endpoint {X Y : OmegaCategory.{u}} (hY : Y.IsTruncated d)
    (P : T.tensor.obj X ⟶ Y) (ε : Bool) :
    (if ε then SSet.ι₁ else SSet.ι₀) ≫ T.nerveCylinder S hY P =
      streetNerveMap ((T.endpoint ε).app X ≫ P) := by
  apply NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  intro F
  cases ε
  · exact T.nerveCylinderSimplex_endpoint S hY P m.unop.len F false
  · exact T.nerveCylinderSimplex_endpoint S hY P m.unop.len F true

def nerveHomotopy {X Y : OmegaCategory.{u}} (hY : Y.IsTruncated d) (P : T.tensor.obj X ⟶ Y) :
    SSet.Homotopy (streetNerveMap ((T.endpoint false).app X ≫ P))
      (streetNerveMap ((T.endpoint true).app X ≫ P)) where
  h := T.nerveCylinder S hY P
  h₀ := T.nerveCylinder_endpoint S hY P false
  h₁ := T.nerveCylinder_endpoint S hY P true
  rel := by
    apply NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨x, hx⟩, θ⟩
    exact False.elim hx

include S in
lemma nerve_weak_iff {X Y : OmegaCategory.{u}} (hY : Y.IsTruncated d) (P : T.tensor.obj X ⟶ Y) :
    simplicialWeakEquivalences (streetNerveMap ((T.endpoint false).app X ≫ P)) ↔
      simplicialWeakEquivalences (streetNerveMap ((T.endpoint true).app X ≫ P)) :=
  simplicialWeakEquivalences_homotopy (T.nerveHomotopy S hY P)

end Thomason.RightIntervalCore

end

noncomputable section
universe u v w z


namespace Thomason.RightIntervalCore
open CategoryTheory Limits OmegaCategory

variable (T : RightIntervalCore.{u})
variable (R : OmegaCategory.{u} ⥤ OmegaCategory.{u}) (adj : T.tensor ⊣ R)

include R adj in

theorem finite_pushout_zigzag
    {n : ℕ} (hS : T.SimplexDescent n) {A B X Y : NCategory.{u} n}
    {i : A ⟶ B} {a : A ⟶ X} {b : B ⟶ Y} {j : X ⟶ Y}
    (sq : IsPushout i a b j)
    (r : B ⟶ A) (hi : i ≫ r = 𝟙 A) (G : B ⟶ B)
    (P₀ P₁ : T.tensor.obj B.val ⟶ B.val)
    (h₀ : (T.endpoint false).app B.val ≫ P₀ = 𝟙 B.val)
    (h₁ : (T.endpoint true).app B.val ≫ P₀ = G)
    (h₂ : (T.endpoint false).app B.val ≫ P₁ = r ≫ i)
    (h₃ : (T.endpoint true).app B.val ≫ P₁ = G)
    (hs₀ : T.tensor.map i ≫ P₀ = T.projection.app A.val ≫ i)
    (hs₁ : T.tensor.map i ≫ P₁ = T.projection.app A.val ≫ i) :
    ∃ (p : Y ⟶ X) (H : Y ⟶ Y), j ≫ p = 𝟙 X ∧
      Nonempty (SSet.Homotopy (𝟙 ((streetNerveFinite n).obj Y))
        ((streetNerveFinite n).map H)) ∧
      Nonempty (SSet.Homotopy ((streetNerveFinite n).map (p ≫ j))
        ((streetNerveFinite n).map H)) := by
  let p : Y ⟶ X := sq.desc (r ≫ a) (𝟙 X) (by
    rw [← Category.assoc, hi, Category.id_comp, Category.comp_id])
  have hpB : b ≫ p = r ≫ a := sq.inl_desc _ _ _
  have hpX : j ≫ p = 𝟙 X := sq.inr_desc _ _ _
  obtain ⟨Q₀, _, _, hB₀, hX₀, _⟩ := T.finite_stationary_gluing R adj sq P₀
    (fun ε => if ε then G else 𝟙 B) (by intro ε; cases ε; exact h₀; exact h₁) hs₀
  obtain ⟨Q₁, _, _, hB₁, hX₁, _⟩ := T.finite_stationary_gluing R adj sq P₁
    (fun ε => if ε then G else r ≫ i) (by intro ε; cases ε; exact h₂; exact h₃) hs₁
  let e₀ (ε : Bool) : Y ⟶ Y := OmegaCategory.Functor.comp ((T.endpoint ε).app Y.val) Q₀
  let e₁ (ε : Bool) : Y ⟶ Y := OmegaCategory.Functor.comp ((T.endpoint ε).app Y.val) Q₁
  have he₀ : e₀ false = 𝟙 Y := by
    apply sq.hom_ext
    · exact hB₀ false
    · exact hX₀ false
  have he₁ : e₁ false = p ≫ j := by
    apply sq.hom_ext
    · rw [← Category.assoc, hpB, Category.assoc, ← sq.w, ← Category.assoc]
      exact hB₁ false
    · rw [← Category.assoc, hpX, Category.id_comp]
      exact hX₁ false
  have he : e₁ true = e₀ true := by
    apply sq.hom_ext
    · exact (hB₁ true).trans (hB₀ true).symm
    · exact (hX₁ true).trans (hX₀ true).symm
  refine ⟨p, e₀ true, hpX, ?_, ?_⟩
  · have h : SSet.Homotopy ((streetNerveFinite n).map (e₀ false))
        ((streetNerveFinite n).map (e₀ true)) := T.nerveHomotopy hS Y.property Q₀
    rw [he₀, (streetNerveFinite n).map_id] at h
    exact ⟨h⟩
  · have h : SSet.Homotopy ((streetNerveFinite n).map (e₁ false))
        ((streetNerveFinite n).map (e₁ true)) := T.nerveHomotopy hS Y.property Q₁
    rw [he₁, he] at h
    exact ⟨h⟩

end Thomason.RightIntervalCore

end

noncomputable section
universe u v w z


namespace Thomason.GreatestNew
open CategoryTheory Limits OmegaCategory AttachmentComparison

variable (T : RightIntervalCore.{u})
variable (R : OmegaCategory.{u} ⥤ OmegaCategory.{u}) (adj : T.tensor ⊣ R)
variable {E : Type u} [PartialOrder E] (A : Set E) (hA : IsLowerSet A)
variable (r : E →o A) (hadj : ∀ (a : A) (e : E), a.val ≤ e ↔ a ≤ r e)
variable (x : E) (hx : IsGreatest Aᶜ x)

include T R adj hA r hadj x hx in

theorem core_finite_pushout_deformation (n : ℕ) (hS : T.SimplexDescent n)
    {X Y : NCategory.{u} n} {a : posetObj n A ⟶ X} {j : X ⟶ Y}
    {b : posetObj n E ⟶ Y} (sq : IsPushout (inc n A) a b j) :
    ∃ (p : Y ⟶ X) (H : Y ⟶ Y), j ≫ p = 𝟙 X ∧
      Nonempty (SSet.Homotopy (𝟙 ((streetNerveFinite n).obj Y))
        ((streetNerveFinite n).map H)) ∧
      Nonempty (SSet.Homotopy ((streetNerveFinite n).map (p ≫ j))
        ((streetNerveFinite n).map H)) := by
  let d₀ := idPrismData A hA x hx
  let d₁ := retractPrismData A hA r hadj x hx
  let i := (OrderEmbedding.subtype (fun element : E => element ∈ A)).toOrderHom
  let r' := retract A hA r hadj x hx
  have hr' : r'.comp i = OrderHom.id := retract_comp_inc A hA r hadj x hx
  have hri : inc n A ≫ posetMap n r' = 𝟙 (posetObj n A) := by
    rw [← finitePosetMap_comp]
    change posetMap n (r'.comp i) = _
    rw [hr', finitePosetMap_id]
  have h₀ : d₀.f.comp i = i := rfl
  have h₁ : d₁.f.comp i = i := by
    ext e
    exact congrArg Subtype.val (retract_old A hA r hadj x hx e)
  have hs₀ := d₀.coreFinitePrism_stationary T R adj n i (fun e => e.property)
  have hs₁ := d₁.coreFinitePrism_stationary T R adj n i (fun e => e.property)
  rw [h₀] at hs₀
  rw [h₁] at hs₁
  exact T.finite_pushout_zigzag R adj hS sq (posetMap n r') hri
    (posetMap n (upper A hA x hx))
    (d₀.coreFinitePrism T R adj n) (d₁.coreFinitePrism T R adj n)
    ((d₀.coreFinitePrism_endpoint_false T R adj n).trans (finitePosetMap_id n E))
    (d₀.coreFinitePrism_endpoint_true T R adj n)
    ((d₁.coreFinitePrism_endpoint_false T R adj n).trans (finitePosetMap_comp n r' i))
    (d₁.coreFinitePrism_endpoint_true T R adj n) hs₀ hs₁

include T R adj hA r hadj x hx in

theorem core_finite_pushout_nerve_weak (n : ℕ) (hS : T.SimplexDescent n)
    {X Y : NCategory.{u} n} {a : posetObj n A ⟶ X} {j : X ⟶ Y}
    {b : posetObj n E ⟶ Y} (sq : IsPushout (inc n A) a b j) :
    simplicialWeakEquivalences ((streetNerveFinite n).map j) := by
  obtain ⟨p,H,hp,⟨H₀⟩,⟨H₁⟩⟩ := core_finite_pushout_deformation T R adj A hA r hadj x hx n hS sq
  exact RightIntervalExtension.finite_nerve_weak_of_zigzag j p H hp H₀ H₁

end Thomason.GreatestNew

end

noncomputable section
universe u v w z


namespace Thomason.Couniversality
open CategoryTheory Limits OmegaCategory Attachments AttachmentComparison

theorem core_finite_poset_couniversal
    (T : RightIntervalCore.{u})
    (R : OmegaCategory.{u} ⥤ OmegaCategory.{u}) (adj : T.tensor ⊣ R)
    (n : ℕ) (hS : T.SimplexDescent n) (hn : 1 ≤ n) {E : Type u} [PartialOrder E] [Finite E]
    (A : Set E) (hA : IsLowerSet A) (r : E →o A)
    (hadj : ∀ (a : A) (e : E), a.val ≤ e ↔ a ≤ r e)
    {X Y : NCategory.{u} n} {a : posetObj n A ⟶ X}
    {j : X ⟶ Y} {v : posetObj n E ⟶ Y} (sq : IsPushout a (inc n A) j v) :
    simplicialWeakEquivalences ((streetNerveFinite n).map j) := by
  classical
  suffices H : ∀ m : ℕ, ∀ (E : Type u) [PartialOrder E] [Finite E], Nat.card E = m →
      ∀ (A : Set E), IsLowerSet A → ∀ (r : E →o A),
      (∀ (a : A) (e : E), a.val ≤ e ↔ a ≤ r e) →
      ∀ {X Y : NCategory.{u} n} (a : posetObj n A ⟶ X) (j : X ⟶ Y)
        (v : posetObj n E ⟶ Y), IsPushout a (inc n A) j v →
        simplicialWeakEquivalences ((streetNerveFinite n).map j) from
    H (Nat.card E) E rfl A hA r hadj a j v sq
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro E _ _ hm A hA r hadj X Y a j v sq
    by_cases he : Aᶜ.Nonempty
    · rcases greatest_or_two_maximal Aᶜ he with ⟨x,hx⟩ | ⟨x,y,hx,hy,hxy⟩
      · exact GreatestNew.core_finite_pushout_nerve_weak T R adj A hA r hadj x hx n hS sq.flip
      · let S₁ : Set E := {x}ᶜ
        let S₂ : Set E := {y}ᶜ
        have h₁ : IsLowerSet S₁ := delete_max_lower (maximal_new_isMax hA hx)
        have h₂ : IsLowerSet S₂ := delete_max_lower (maximal_new_isMax hA hy)
        have hA₁ : A ⊆ S₁ := by
          intro z hz heq
          change z = x at heq
          exact hx.1 (heq ▸ hz)
        have hA₂ : A ⊆ S₂ := by
          intro z hz heq
          change z = y at heq
          exact hy.1 (heq ▸ hz)
        have hc : S₁ ∪ S₂ = Set.univ := by
          apply Set.eq_univ_of_forall
          intro z
          change z ≠ x ∨ z ≠ y
          by_cases hz : z = x
          · exact Or.inr (fun heq => hxy (hz.symm.trans heq))
          · exact Or.inl hz
        obtain ⟨T₁,T₂,hT₁,hT₂,hTc,hp₁,hp₂,hp₃⟩ :=
          sieve_finite_attachment_covers n hn A S₁ S₂ h₁ h₂ hA₁ hA₂ hc a j v sq
        have hpiece (S : Set E) (hAS : A ⊆ S) (e : E) (he : e ∉ S)
            (Z : Set Y.val.Objects) (hp : IsPosetFiniteAttachmentPiece n A S hAS a j v Z) :
            ∃ (jS : X ⟶ fullFinite n Y Z), jS ≫ fullFiniteInclusion n Y Z = j ∧
              simplicialWeakEquivalences ((streetNerveFinite n).map jS) := by
          obtain ⟨jS,vS,hjS,hvS,sqS⟩ := hp
          refine ⟨jS,hjS,?_⟩
          let eS := nestedOldIso (categorificationFinite n) A S hAS
          have sqS' : IsPushout (eS.hom ≫ a) (inc n {s : S | s.val ∈ A}) jS vS := by
            apply sqS.of_iso' eS (Iso.refl _) (Iso.refl _) (Iso.refl _)
            · simp
            · simp only [Iso.refl_hom, Category.comp_id]
              exact nestedOldIso_inc (categorificationFinite n) A S hAS
            · simp
            · simp
          exact ih (Nat.card S) (hm ▸ Finite.card_subtype_lt he) S rfl
            {s : S | s.val ∈ A} (restricted_lower hA S)
            (restrictedRetract A S hAS r) (restricted_adjoint A S hAS r hadj)
            (eS.hom ≫ a) jS vS sqS'
        obtain ⟨j₁,hj₁,hw₁⟩ := hpiece S₁ hA₁ x (by simp [S₁]) T₁ hp₁
        obtain ⟨j₂,hj₂,hw₂⟩ := hpiece S₂ hA₂ y (by simp [S₂]) T₂ hp₂
        obtain ⟨j₃,hj₃,hw₃⟩ := hpiece (S₁ ∩ S₂) (fun _ ha => ⟨hA₁ ha,hA₂ ha⟩)
          x (by simp [S₁]) (T₁ ∩ T₂) hp₃
        apply weak_of_full_sieve_cover hT₁ hT₂ hTc ((streetNerveFinite n).map j)
          ((streetNerveFinite n).map j₁) ((streetNerveFinite n).map j₂)
          ((streetNerveFinite n).map j₃) _ _ _ hw₁ hw₂ hw₃
        · exact (Functor.map_comp (streetNerveFinite n) _ _).symm.trans
            (congrArg (fun f : X ⟶ Y => (streetNerveFinite n).map f) hj₁)
        · exact (Functor.map_comp (streetNerveFinite n) _ _).symm.trans
            (congrArg (fun f : X ⟶ Y => (streetNerveFinite n).map f) hj₂)
        · exact (Functor.map_comp (streetNerveFinite n) _ _).symm.trans
            (congrArg (fun f : X ⟶ Y => (streetNerveFinite n).map f) hj₃)
    · have ha : ∀ e, e ∈ A := by
        intro e
        by_contra h
        exact he ⟨e,h⟩
      have : IsIso (inc n A) := isIso_subtype_all (categorificationFinite n) A ha
      have : IsIso j := sq.isIso_inl_of_isIso
      exact simplicialWeakEquivalences.of_isIso _

end Thomason.Couniversality

end

noncomputable section
universe u v w z


namespace Thomason.Couniversality
open CategoryTheory Limits FilteredPosets FilteredPushouts

theorem core_poset_couniversal
    (T : RightIntervalCore.{u})
    (R : OmegaCategory.{u} ⥤ OmegaCategory.{u}) (adj : T.tensor ⊣ R)
    (n : ℕ) (hS : T.SimplexDescent n) (hn : 1 ≤ n) {E : Type u} [PartialOrder E]
    (A : Set E) (hA : IsLowerSet A) (r : E →o A)
    (hadj : ∀ (a : A) (e : E), a.val ≤ e ↔ a ≤ r e)
    {X Y : OmegaCategory.NCategory.{u} n} {a : AttachmentComparison.posetObj n A ⟶ X}
    {j : X ⟶ Y} {v : AttachmentComparison.posetObj n E ⟶ Y}
    (sq : IsPushout a (AttachmentComparison.inc n A) j v) :
    simplicialWeakEquivalences ((streetNerveFinite n).map j) := by
  let := (categorificationFiniteAdjunction n).leftAdjoint_preservesColimits
  exact couniversal_of_finite (categorificationFinite n) (streetNerveFinite n)
    (fun P _ _ A hA r hr _ _ a j v sq =>
      core_finite_poset_couniversal T R adj n hS hn A hA r hr sq) A hA r hadj a j v sq

end Thomason.Couniversality

end

noncomputable section
universe u v w z


namespace Thomason.AttachmentComparison
open CategoryTheory Limits OmegaCategory Attachments Couniversality

lemma core_gray_piece_couniversal (T : RightIntervalCore.{u})
    (R : OmegaCategory.{u} ⥤ OmegaCategory.{u}) (adj : T.tensor ⊣ R)
    (n : ℕ) (hS : T.SimplexDescent n) (hn : 1 ≤ n) {B : Type u} [PartialOrder B]
    (A S : Set B) (hA : IsLowerSet A) (hAS : A ⊆ S)
    (r : S →o A) (hadj : ∀ (a : A) (s : S), a.val ≤ s.val ↔ a ≤ r s)
    {X Y : NCategory.{u} n} (a : posetObj n A ⟶ X)
    (j : X ⟶ Y) (v : posetObj n S ⟶ Y)
    (sq : IsPushout a (sb n A S hAS) j v) :
    simplicialWeakEquivalences ((streetNerveFinite n).map j) := by
  let e := nestedOldIso (categorificationFinite n) A S hAS
  let r' : S →o {s : S | s.val ∈ A} :=
    ⟨fun s => ⟨⟨(r s).val,hAS (r s).property⟩,(r s).property⟩,
      fun _ _ h => r.monotone h⟩
  have sq' : IsPushout (e.hom ≫ a) (inc n {s : S | s.val ∈ A}) j v := by
    apply sq.of_iso' e (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · simp
    · simp only [Iso.refl_hom,Category.comp_id]
      exact nestedOldIso_inc (categorificationFinite n) A S hAS
    · simp
    · simp
  exact core_poset_couniversal T R adj n hS hn {s : S | s.val ∈ A}
    (restricted_lower hA S) r' (fun a s => hadj ⟨a.val.val,a.property⟩ s) sq'

lemma core_gray_comparison_local (T : RightIntervalCore.{u})
    (R : OmegaCategory.{u} ⥤ OmegaCategory.{u}) (adj : T.tensor ⊣ R)
    (n : ℕ) (hS : T.SimplexDescent n) (hn : 1 ≤ n) {B : Type u} [PartialOrder B]
    (A : Set B) (hA : IsLowerSet A)
    (r : upward A →o A)
    (hadj : ∀ (a : A) (z : upward A), a.val ≤ z.val ↔ a ≤ r z)
    {X Y : NCategory.{u} n} (a : posetObj n A ⟶ X)
    (j : X ⟶ Y) (v : posetObj n B ⟶ Y) (sc : IsPushout a (inc n A) j v)
    {P : SSet.{u}} {lX : (streetNerveFinite n).obj X ⟶ P}
    {lB : (streetNerveFinite n).obj (posetObj n B) ⟶ P}
    (ss : IsPushout ((streetNerveFinite n).map a) ((streetNerveFinite n).map (inc n A)) lX lB)
    (F : P ⟶ (streetNerveFinite n).obj Y)
    (hFX : lX ≫ F = (streetNerveFinite n).map j)
    (hFB : lB ≫ F = (streetNerveFinite n).map v) : simplicialWeakEquivalences F := by
  let Z := upward A
  let C := Aᶜ
  have hAZ : A ⊆ Z := fun x hx => ⟨x,hx,le_rfl⟩
  have hZ : IsUpperSet Z := by
    intro x y hxy hx
    obtain ⟨a,ha,hax⟩ := hx
    exact ⟨a,ha,hax.trans hxy⟩
  have hC : IsUpperSet C := isUpperSet_compl.mpr hA
  have hcov : Z ∪ C = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    by_cases hx : x ∈ A
    · exact Or.inl (hAZ hx)
    · exact Or.inr hx
  obtain ⟨YZ,jZ,vZ,uZ,scZ,hj,hv,sq⟩ :=
    attachment_nerve_cover n hn A Z C hZ hC hAZ disjoint_compl_right hcov a j v sc
  let N := streetNerveFinite n
  let e := N.map (sb n A Z hAZ)
  let b := N.map a
  let PZ := pushout b e
  let xZ := pushout.inl b e
  let zZ := pushout.inr b e
  let sZ := IsPushout.of_hasPushout b e
  let FZ : PZ ⟶ N.obj YZ := sZ.desc (N.map jZ) (N.map vZ) (by
    rw [← N.map_comp, ← N.map_comp, scZ.w])
  have hFZX : xZ ≫ FZ = N.map jZ := sZ.inl_desc _ _ _
  have hFZZ : zZ ≫ FZ = N.map vZ := sZ.inr_desc _ _ _
  have hwj : simplicialWeakEquivalences (N.map jZ) :=
    core_gray_piece_couniversal T R adj n hS hn A Z hA hAZ r hadj a jZ vZ scZ
  have hwe : simplicialWeakEquivalences e :=
    core_gray_piece_couniversal T R adj n hS hn A Z hA hAZ r hadj
      (𝟙 _) (sb n A Z hAZ) (𝟙 _) IsPushout.of_id_fst
  have hcE : Mono e := by
    let e' := nestedOldIso (categorificationFinite n) A Z hAZ
    have he' : sb n A Z hAZ = e'.inv ≫ inc n {z : Z | z.val ∈ A} := by
      calc
        _ = e'.inv ≫ (e'.hom ≫ sb n A Z hAZ) := by simp
        _ = _ := congrArg (e'.inv ≫ ·) (nestedOldIso_inc (categorificationFinite n) A Z hAZ)
    have : Mono (N.map (inc n {z : Z | z.val ∈ A})) :=
      finite_nerve_attachment_mono n hn _ (restricted_lower hA Z)
        (𝟙 _) _ (𝟙 _) IsPushout.of_id_fst
    dsimp [e]
    rw [he',CategoryTheory.Functor.map_comp]
    infer_instance
  have hwx : simplicialWeakEquivalences xZ := by
    have he : SSet.anodyneExtensions e := KanQuillen.anodyne_class.symm ▸ ⟨hcE,hwe⟩
    exact KanQuillen.anodyne_weak _ (SSet.anodyneExtensions.of_isPushout sZ he)
  have hwFZ : simplicialWeakEquivalences FZ :=
    simplicialWeakEquivalences.of_precomp xZ FZ hwx (hFZX ▸ hwj)
  let pZ : PZ ⟶ P := sZ.desc lX (N.map (inc n Z) ≫ lB) (by
    rw [← Category.assoc, ← N.map_comp, sb_inc]
    exact ss.w)
  have hpZX : xZ ≫ pZ = lX := sZ.inl_desc _ _ _
  have hpZZ : zZ ≫ pZ = N.map (inc n Z) ≫ lB := sZ.inr_desc _ _ _
  have ss' : IsPushout b (e ≫ N.map (inc n Z)) (xZ ≫ pZ) lB := by
    rw [hpZX, ← N.map_comp, sb_inc]
    exact ss
  have sr : IsPushout zZ (N.map (inc n Z)) pZ lB := ss'.of_top hpZZ sZ
  have sp := (poset_nerve_cover n hn Z C hZ hC hcov).paste_horiz sr
  let k := N.map (sb n (Z ∩ C) Z Set.inter_subset_left) ≫ zZ
  let c := N.map (sb n (Z ∩ C) C Set.inter_subset_right)
  have hc : Mono c := finite_nerve_inter_upper_mono n hn Z C hZ
  have hk : k ≫ FZ = N.map (sb n (Z ∩ C) Z Set.inter_subset_left ≫ vZ) := by
    rw [show k = N.map (sb n (Z ∩ C) Z Set.inter_subset_left) ≫ zZ from rfl,
      Category.assoc, hFZZ, ← N.map_comp]
  have sq' : IsPushout (k ≫ FZ) c (N.map uZ) (N.map (inc n C ≫ v)) := by
    rw [hk]
    exact sq
  have hFpZ : pZ ≫ F = FZ ≫ N.map uZ := by
    apply sZ.hom_ext
    · rw [← Category.assoc, hpZX, ← Category.assoc xZ, hFZX, ← N.map_comp, hj]
      exact hFX
    · rw [← Category.assoc, hpZZ, Category.assoc, hFB,
        ← Category.assoc zZ, hFZZ, ← N.map_comp, ← N.map_comp, hv]
  have hFC : (N.map (inc n C) ≫ lB) ≫ F = N.map (inc n C ≫ v) := by
    rw [Category.assoc, hFB, ← N.map_comp]
  exact KanLocal.local_weak F (KanLocal.local_pushout_map k c FZ
    (GeometricRecognition.weak_local FZ hwFZ) sp sq' F hFpZ hFC)

end Thomason.AttachmentComparison

end

end OAI
