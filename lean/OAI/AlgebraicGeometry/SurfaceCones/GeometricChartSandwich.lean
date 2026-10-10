import OAI.AlgebraicGeometry.SurfaceCones.AffineNaturalPower

namespace OAI

/-!
# Cartier twists on affine charts and derived restriction

This development accompanies *A Complete Local Domain without a Small
Cohen–Macaulay Module* (OpenAI, 2026).
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualCartier
open Scheme.Modules ActualSheafTensor CartierImageFiltration
variable {X Y : Scheme.{0}} [IsLocallyNoetherian Y]
    (g : X ⟶ Y) [IsClosedImmersion g]
    {R : CommRingCat.{0}} (f : Spec R ⟶ Y) [IsOpenImmersion f]
    (eL : (restrictFunctor f).obj (idealSheaf g) ≅
      SheafOfModules.unit (Spec R).ringCatSheaf)

private local instance chartSectionModule {Z : Scheme.{0}} (M : Z.Modules)
    (U : Z.Opensᵒᵖ) : Module (Z.sheaf.obj.obj U) (M.val.obj U) := (M.val.obj U).isModule

include eL in
/-- Uniform affine Cartier lattice embeddings retain the fixed isomorphism
on the entire geometric puncture of the chart. -/
lemma exists_chart_sandwich_on_geometric_puncture (M N : Y.Modules)
    [M.IsFinitePresentation] [N.IsFinitePresentation]
    (hM : ∀ V, Module.IsTorsionFree (Y.sheaf.obj.obj V) (M.val.obj V))
    (hN : ∀ V, Module.IsTorsionFree (Y.sheaf.obj.obj V) (N.val.obj V))
    (e : M.over (ActualOpenSupport.complement g) ≅
      N.over (ActualOpenSupport.complement g)) :
    let L := (restrictFunctor f).obj (idealSheaf g)
    let i := restrictedIdeal f (idealι g)
    let W := ActualOpenSupport.complement g
    let U := f ⁻¹ᵁ W
    let T := tensorLeft (Spec R).sheaf L
    let act := idealAction (Spec R).sheaf i
    let Mf := (restrictFunctor f).obj M
    let Nf := (restrictFunctor f).obj N
    let ep := ActualOpenComparison.pullOverIso f U W (f.image_preimage_le W) e
    ∃ k : ℕ, ∀ n : ℕ, k ≤ n →
      ∃ (a : (power T n).obj Mf ⟶ Nf) (b : (power T n).obj Nf ⟶ Mf),
        Mono a ∧ Mono b ∧
        a.over U = ((powerAction T act n).app Mf).over U ≫ ep.hom ∧
        b.over U = ((powerAction T act n).app Nf).over U ≫ ep.inv := by
  dsimp only
  generalize_proofs hSheaf hLocal h
  revert h
  rw [← chart_equation_puncture_eq_preimage g f eL]
  intro h
  exact exists_chart_uniform_sandwich g f eL M N hM hN e
end ActualCartier

end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualCartier
open Scheme.Modules ActualSheafTensor CartierImageFiltration
variable {X Y : Scheme.{0}} [IsLocallyNoetherian Y]
    (g : X ⟶ Y) [IsClosedImmersion g]
    {R : CommRingCat.{0}} (f : Spec R ⟶ Y) [IsOpenImmersion f]
    (eL : (restrictFunctor f).obj (idealSheaf g) ≅
      SheafOfModules.unit (Spec R).ringCatSheaf)
attribute [local instance] chartSectionModule

include eL in
/-- Affine denominator clearing for restrictions of global Cartier twists.
The embeddings agree with the fixed puncture identification,
and the tensor comparison intertwines their iterated actions. -/
lemma exists_chart_global_power_sandwich (M N : Y.Modules)
    [M.IsFinitePresentation] [N.IsFinitePresentation]
    (hM : ∀ V, Module.IsTorsionFree (Y.sheaf.obj.obj V) (M.val.obj V))
    (hN : ∀ V, Module.IsTorsionFree (Y.sheaf.obj.obj V) (N.val.obj V))
    (e : M.over (ActualOpenSupport.complement g) ≅
      N.over (ActualOpenSupport.complement g)) :
    let T := tensorLeft Y.sheaf (idealSheaf g)
    let act := idealAction Y.sheaf (idealι g)
    let F := restrictFunctor f
    let W := ActualOpenSupport.complement g
    let U := f ⁻¹ᵁ W
    let ep := ActualOpenComparison.pullOverIso f U W (f.image_preimage_le W) e
    ∃ k : ℕ, ∀ n : ℕ, k ≤ n →
      ∃ (a : F.obj ((power T n).obj M) ⟶ F.obj N)
        (b : F.obj ((power T n).obj N) ⟶ F.obj M),
        Mono a ∧ Mono b ∧
        a.over U = (F.map ((powerAction T act n).app M)).over U ≫ ep.hom ∧
        b.over U = (F.map ((powerAction T act n).app N)).over U ≫ ep.inv := by
  let T := tensorLeft Y.sheaf (idealSheaf g)
  let F := restrictFunctor f
  let S := tensorLeft (Spec R).sheaf (F.obj (idealSheaf g))
  let i := idealAction Y.sheaf (idealι g)
  let j := idealAction (Spec R).sheaf (restrictedIdeal f (idealι g))
  let c := powerComparison T S F (tensorOpenRestrictNatIso f (idealSheaf g))
  have hc (n : ℕ) (A : Y.Modules) :
      (c n A).hom ≫ (powerAction S j n).app (F.obj A) =
        F.map ((powerAction T i n).app A) :=
    powerComparison_action T S F (tensorOpenRestrictNatIso f (idealSheaf g))
      i j (tensorOpenRestrict_action f (idealι g)) n A
  obtain ⟨k, hk⟩ := exists_chart_sandwich_on_geometric_puncture g f eL M N hM hN e
  refine ⟨k, fun n hn => ?_⟩
  obtain ⟨a, b, ha, hb, hae, hbe⟩ := hk n hn
  change (SheafOfModules.overFunctor (ringSheaf (Spec R).sheaf) _).map a =
    (SheafOfModules.overFunctor (ringSheaf (Spec R).sheaf) _).map
      ((powerAction S j n).app (F.obj M)) ≫ _ at hae
  change (SheafOfModules.overFunctor (ringSheaf (Spec R).sheaf) _).map b =
    (SheafOfModules.overFunctor (ringSheaf (Spec R).sheaf) _).map
      ((powerAction S j n).app (F.obj N)) ≫ _ at hbe
  have : Mono a := ha
  have : Mono b := hb
  refine ⟨(c n M).hom ≫ a, (c n N).hom ≫ b,
    mono_comp' (@IsIso.mono_of_iso _ _ _ _ _ (c n M).isIso_hom) ha,
    mono_comp' (@IsIso.mono_of_iso _ _ _ _ _ (c n N).isIso_hom) hb, ?_, ?_⟩
  · change (SheafOfModules.overFunctor _ _).map ((c n M).hom ≫ a) = _
    erw [Functor.map_comp, hae, ← Category.assoc, ← Functor.map_comp, hc]
  · change (SheafOfModules.overFunctor _ _).map ((c n N).hom ≫ b) = _
    erw [Functor.map_comp, hbe, ← Category.assoc, ← Functor.map_comp, hc]
end ActualCartier

end

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
open scoped TensorProduct
namespace ActualSheafTensor
private local instance projectionSectionModule {Z : Scheme.{0}} (M : Z.Modules)
    (U : Z.Opensᵒᵖ) : Module (Z.sheaf.obj.obj U) (M.val.obj U) := (M.val.obj U).isModule

private local instance projectionOpenSectionModule {Z : Scheme.{0}} (M : Z.Modules)
    (U : Z.Opens) : Module Γ(Z, U) (M.val.obj (op U)) := (M.val.obj (op U)).isModule

open Scheme.Modules
variable {X Y : Scheme.{0}} (f : X ⟶ Y) (L : Y.Modules) (N : X.Modules)
local instance : MonoidalCategory (PresheafOfModules.{0} Y.ringCatSheaf.obj) :=
  inferInstanceAs (MonoidalCategory (PresheafOfModules.{0}
    (Y.sheaf.obj ⋙ forget₂ CommRingCat RingCat)))
local instance : MonoidalCategory (PresheafOfModules.{0} X.ringCatSheaf.obj) :=
  inferInstanceAs (MonoidalCategory (PresheafOfModules.{0}
    (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)))

def pullbackUnitSemilinear (U : Y.Opens) :
    L.val.obj (op U) →ₛₗ[(f.app U).hom]
      ((Scheme.Modules.pullback f).obj L).val.obj (op (f ⁻¹ᵁ U)) where
  toFun := ((pullbackPushforwardAdjunction f).unit.app L).val.app (op U)
  map_add' := (((pullbackPushforwardAdjunction f).unit.app L).val.app (op U)).hom.map_add
  map_smul' := (((pullbackPushforwardAdjunction f).unit.app L).val.app (op U)).hom.map_smul

def pushforwardSemilinear (U : Y.Opens) :
    ((pushforward f).obj N).val.obj (op U) →ₛₗ[(f.app U).hom]
      N.val.obj (op (f ⁻¹ᵁ U)) where
  toFun := id
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def tensorProjectionApp (U : Y.Opens) :
    (L.val.obj (op U) ⊗[Y.sheaf.obj.obj (op U)] ((pushforward f).obj N).val.obj (op U)) →ₗ[
      Y.sheaf.obj.obj (op U)]
      ((pushforward f).obj (tensor X.sheaf ((Scheme.Modules.pullback f).obj L) N)).val.obj (op U) := by
  let : Module Γ(Y, U) (L.val.obj (op U)) := (L.val.obj (op U)).isModule
  let : Module Γ(Y, U) (((pushforward f).obj N).val.obj (op U)) :=
    (((pushforward f).obj N).val.obj (op U)).isModule
  let P := PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.sheaf.obj)
    ((Scheme.Modules.pullback f).obj L).val N.val
  let η := (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P
  let : Module Γ(Y, U)
      (L.val.obj (op U) ⊗[Y.sheaf.obj.obj (op U)] ((pushforward f).obj N).val.obj (op U)) :=
    inferInstanceAs (Module (Y.sheaf.obj.obj (op U))
      (L.val.obj (op U) ⊗[Y.sheaf.obj.obj (op U)] ((pushforward f).obj N).val.obj (op U)))
  let : Module Γ(X, f ⁻¹ᵁ U)
      (((Scheme.Modules.pullback f).obj L).val.obj (op (f ⁻¹ᵁ U)) ⊗[X.sheaf.obj.obj (op (f ⁻¹ᵁ U))]
        N.val.obj (op (f ⁻¹ᵁ U))) :=
    inferInstanceAs (Module (X.sheaf.obj.obj (op (f ⁻¹ᵁ U)))
      (((Scheme.Modules.pullback f).obj L).val.obj (op (f ⁻¹ᵁ U)) ⊗[X.sheaf.obj.obj (op (f ⁻¹ᵁ U))]
        N.val.obj (op (f ⁻¹ᵁ U))))
  let t : (L.val.obj (op U) ⊗[Y.sheaf.obj.obj (op U)] ((pushforward f).obj N).val.obj (op U))
      →ₛₗ[(f.app U).hom]
      (((Scheme.Modules.pullback f).obj L).val.obj (op (f ⁻¹ᵁ U)) ⊗[X.sheaf.obj.obj (op (f ⁻¹ᵁ U))]
        N.val.obj (op (f ⁻¹ᵁ U))) :=
    TensorProduct.map (pullbackUnitSemilinear f L U) (pushforwardSemilinear f N U)
  exact {
    toFun := fun z => η.app (op (f ⁻¹ᵁ U)) (t z)
    map_add' := by
      intro x y
      exact (congrArg (η.app (op (f ⁻¹ᵁ U))) (t.map_add x y)).trans
        ((η.app (op (f ⁻¹ᵁ U))).hom.map_add (t x) (t y))
    map_smul' := by
      intro r z
      exact (congrArg (η.app (op (f ⁻¹ᵁ U))) (t.map_smulₛₗ r z)).trans
        ((η.app (op (f ⁻¹ᵁ U))).hom.map_smul ((f.app U) r) (t z)) }

end ActualSheafTensor

end

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
open scoped TensorProduct
namespace ActualSheafTensor
attribute [local instance] projectionSectionModule projectionOpenSectionModule
open Scheme.Modules
variable {X Y : Scheme.{0}} (f : X ⟶ Y) (L : Y.Modules) (N : X.Modules)
local instance : MonoidalCategory (PresheafOfModules.{0} Y.ringCatSheaf.obj) :=
  inferInstanceAs (MonoidalCategory (PresheafOfModules.{0}
    (Y.sheaf.obj ⋙ forget₂ CommRingCat RingCat)))
local instance : MonoidalCategory (PresheafOfModules.{0} X.ringCatSheaf.obj) :=
  inferInstanceAs (MonoidalCategory (PresheafOfModules.{0}
    (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)))

def tensorProjectionPresheaf :
    PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := Y.sheaf.obj) L.val ((pushforward f).obj N).val ⟶
    ((pushforward f).obj (tensor X.sheaf ((Scheme.Modules.pullback f).obj L) N)).val where
  app U := ConcreteCategory.ofHom (C := ModuleCat (Y.sheaf.obj.obj U))
    (tensorProjectionApp f L N U.unop)
  naturality {U V} h := by
    let P := PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := Y.sheaf.obj)
      L.val ((pushforward f).obj N).val
    let Q := ((pushforward f).obj (tensor X.sheaf ((Scheme.Modules.pullback f).obj L) N)).val
    let B : ModuleCat (Y.ringCatSheaf.obj.obj U) :=
      (ModuleCat.restrictScalars (Y.ringCatSheaf.obj.map h).hom).obj (Q.obj V)
    let a : P.obj U ⟶ B := P.map h ≫
      (ModuleCat.restrictScalars (Y.ringCatSheaf.obj.map h).hom).map
        (ConcreteCategory.ofHom (C := ModuleCat (Y.sheaf.obj.obj V)) (tensorProjectionApp f L N V.unop))
    let b : P.obj U ⟶ B :=
      ConcreteCategory.ofHom (C := ModuleCat (Y.sheaf.obj.obj U)) (tensorProjectionApp f L N U.unop) ≫ Q.map h
    let : Module (Y.sheaf.obj.obj U) B := B.isModule
    let : Module (Y.sheaf.obj.obj U) (P.obj U) := (P.obj U).isModule
    change a = b
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.inductionOn (R := Y.sheaf.obj.obj U) with
    | tmul x y =>
      let P := PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.sheaf.obj)
        ((Scheme.Modules.pullback f).obj L).val N.val
      let η := (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P
      let u := (pullbackPushforwardAdjunction f).unit.app L
      let a := ((TopologicalSpace.Opens.map f.base).map h.unop).op
      have hu := PresheafOfModules.naturality_apply u.val h x
      have hη := PresheafOfModules.naturality_apply η a (u.val.app U x ⊗ₜ[X.sheaf.obj.obj (op (f ⁻¹ᵁ U.unop))] y)
      exact (congrArg (fun z => η.app (op (f ⁻¹ᵁ V.unop))
        (z ⊗ₜ[X.sheaf.obj.obj (op (f ⁻¹ᵁ V.unop))] N.val.map a y)) hu).trans hη
    | add x y hx hy =>
      exact (a.hom.map_add x y).trans
        ((congrArg₂ (· + ·) hx hy).trans (b.hom.map_add x y).symm)

/-- The canonical projection morphism for the tensor sheaves. -/
def tensorProjection : tensor Y.sheaf L ((pushforward f).obj N) ⟶
    (pushforward f).obj (tensor X.sheaf ((Scheme.Modules.pullback f).obj L) N) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).homEquiv _ _).symm
    (tensorProjectionPresheaf f L N)

lemma tensorProjection_pure (U : Y.Opens) (x : L.val.obj (op U))
    (y : ((pushforward f).obj N).val.obj (op U)) :
    (tensorProjection f L N).val.app (op U)
      (((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app
        (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := Y.sheaf.obj)
          L.val ((pushforward f).obj N).val)).app (op U) (x ⊗ₜ[Y.sheaf.obj.obj (op U)] y)) =
      tensorProjectionApp f L N U (x ⊗ₜ[Y.sheaf.obj.obj (op U)] y) := by
  have h :
      (PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).homEquiv
        (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := Y.sheaf.obj)
          L.val ((pushforward f).obj N).val)
        ((pushforward f).obj (tensor X.sheaf ((Scheme.Modules.pullback f).obj L) N))
        (tensorProjection f L N) = tensorProjectionPresheaf f L N :=
    Equiv.apply_symm_apply _ _
  erw [Adjunction.homEquiv_unit] at h
  exact congrArg (fun g => g.app (op U) (x ⊗ₜ[Y.sheaf.obj.obj (op U)] y)) h
end ActualSheafTensor

end

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
open scoped TensorProduct
namespace ActualSheafTensor
attribute [local instance] projectionSectionModule projectionOpenSectionModule
open Scheme.Modules
variable {X Y : Scheme.{0}} (f : X ⟶ Y)

lemma tensorProjection_pure' (L : Y.Modules) (N : X.Modules)
    (U : Y.Opens) (x : L.val.obj (op U))
    (y : ((pushforward f).obj N).val.obj (op U)) :
    (tensorProjection f L N).val.app (op U)
      (pure Y.sheaf L ((pushforward f).obj N) (op U) x y) =
    pure X.sheaf ((Scheme.Modules.pullback f).obj L) N (op (f ⁻¹ᵁ U))
      (((pullbackPushforwardAdjunction f).unit.app L).val.app (op U) x) y := by
  exact tensorProjection_pure f L N U x y

lemma tensorProjection_naturality_left {L L' : Y.Modules} (e : L ⟶ L') (N : X.Modules) :
    (tensorLeftMap Y.sheaf e).app ((pushforward f).obj N) ≫ tensorProjection f L' N =
      tensorProjection f L N ≫ (pushforward f).map
        ((tensorLeftMap X.sheaf ((Scheme.Modules.pullback f).map e)).app N) := by
  apply tensor_hom_ext Y.sheaf
  intro U x y
  let V := op (f ⁻¹ᵁ U.unop)
  let P := tensorProjection f L N
  let P' := tensorProjection f L' N
  let aY := (tensorLeftMap Y.sheaf e).app ((pushforward f).obj N)
  let aX := (tensorLeftMap X.sheaf ((Scheme.Modules.pullback f).map e)).app N
  let u := (pullbackPushforwardAdjunction f).unit.app L
  let u' := (pullbackPushforwardAdjunction f).unit.app L'
  have hy := tensorLeftMap_pure Y.sheaf e ((pushforward f).obj N) U x y
  have hp := tensorProjection_pure' f L N U.unop x y
  have hp' := tensorProjection_pure' f L' N U.unop (e.val.app U x) y
  have hx := tensorLeftMap_pure X.sheaf ((Scheme.Modules.pullback f).map e) N V
    (u.val.app U x) y
  have hu := congrArg (fun g => g.val.app U x) ((pullbackPushforwardAdjunction f).unit.naturality e)
  change u'.val.app U (e.val.app U x) =
    ((Scheme.Modules.pullback f).map e).val.app V (u.val.app U x) at hu
  change P'.val.app U (aY.val.app U (pure Y.sheaf L ((pushforward f).obj N) U x y)) =
    aX.val.app V (P.val.app U (pure Y.sheaf L ((pushforward f).obj N) U x y))
  exact (congrArg (P'.val.app U) hy).trans (hp'.trans
    ((congrArg (fun z => pure X.sheaf ((Scheme.Modules.pullback f).obj L') N V z y) hu).trans
      (hx.symm.trans (congrArg (aX.val.app V) hp.symm))))
end ActualSheafTensor

end

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
open scoped TensorProduct
namespace ActualSheafTensor
attribute [local instance] projectionSectionModule projectionOpenSectionModule
open Scheme.Modules
variable {X Y : Scheme.{0}} (f : X ⟶ Y)

lemma opensMap_final : (TopologicalSpace.Opens.map f.base).Final := by
  have hp : PreservesLimit (Functor.empty Y.Opens) (TopologicalSpace.Opens.map f.base) :=
    preservesLimit_of_preserves_limit_cone (isTerminalTop : IsTerminal (⊤ : Y.Opens))
      ((isLimitMapConeEmptyConeEquiv _ _).symm
        (by simpa only [TopologicalSpace.Opens.map_top] using
          (isTerminalTop : IsTerminal (⊤ : X.Opens))))
  infer_instance

/-- Canonical identification of the pullback of the unit sheaf. -/
def sheafPullbackUnitIso : (Scheme.Modules.pullback f).obj (SheafOfModules.unit _) ≅
    SheafOfModules.unit X.ringCatSheaf := by
  let : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    (pullbackPushforwardAdjunction f).isRightAdjoint
  have hp : PreservesLimit (Functor.empty Y.Opens) (TopologicalSpace.Opens.map f.base) :=
    preservesLimit_of_preserves_limit_cone (isTerminalTop : IsTerminal (⊤ : Y.Opens))
      ((isLimitMapConeEmptyConeEquiv _ _).symm
        (by simpa only [TopologicalSpace.Opens.map_top] using
          (isTerminalTop : IsTerminal (⊤ : X.Opens))))
  have : (TopologicalSpace.Opens.map f.base).Final := inferInstance
  have hi : IsIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) :=
    SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal
      (F := TopologicalSpace.Opens.map f.base) f.toRingCatSheafHom
  exact @asIso _ _ _ _ (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) hi

lemma sheafPullbackUnitIso_unit (U : Y.Opens) (r : Y.sheaf.obj.obj (op U)) :
    (sheafPullbackUnitIso f).hom.val.app (op (f ⁻¹ᵁ U))
      (((pullbackPushforwardAdjunction f).unit.app (SheafOfModules.unit _)).val.app (op U) r) =
      (f.app U) r := by
  let : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    (pullbackPushforwardAdjunction f).isRightAdjoint
  have h := SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    f.toRingCatSheafHom
  erw [Adjunction.homEquiv_unit] at h
  exact congrArg (fun g => g.val.app (op U) r) h

/-- Target trivialization for the projection formula with unit coefficients. -/
def tensorProjectionUnitTargetIso (N : X.Modules) :
    (pushforward f).obj (tensor X.sheaf
      ((Scheme.Modules.pullback f).obj (SheafOfModules.unit _)) N) ≅
      (pushforward f).obj N :=
  (pushforward f).mapIso
    (((tensorLeftIso X.sheaf (sheafPullbackUnitIso f)).app N) ≪≫ leftUnitIso X.sheaf N)

lemma tensorProjection_unit (N : X.Modules) :
    tensorProjection f (SheafOfModules.unit _) N ≫
      (tensorProjectionUnitTargetIso f N).hom = (leftUnitIso Y.sheaf ((pushforward f).obj N)).hom := by
  apply tensor_hom_ext Y.sheaf
  intro U r y
  let V := op (f ⁻¹ᵁ U.unop)
  let L := SheafOfModules.unit Y.ringCatSheaf
  let P := tensorProjection f L N
  let i := (sheafPullbackUnitIso f).hom
  let a := (tensorLeftMap X.sheaf i).app N
  let u := (pullbackPushforwardAdjunction f).unit.app L
  let leftX := (leftUnitIso X.sheaf N).hom
  have hp := tensorProjection_pure' f L N U.unop r y
  have hm := tensorLeftMap_pure X.sheaf i N V (u.val.app U r) y
  have hx := leftUnitIso_pure X.sheaf N V (i.val.app V (u.val.app U r)) y
  have hu := sheafPullbackUnitIso_unit f U.unop r
  have hy := leftUnitIso_pure Y.sheaf ((pushforward f).obj N) U r y
  change leftX.val.app V (a.val.app V
    (P.val.app U (pure Y.sheaf L ((pushforward f).obj N) U r y))) = _
  exact (congrArg (fun z => leftX.val.app V (a.val.app V z)) hp).trans
    ((congrArg (leftX.val.app V) hm).trans
      (hx.trans ((congrArg (fun z : X.sheaf.obj.obj V =>
        @SMul.smul (X.sheaf.obj.obj V) (N.val.obj V) (N.val.obj V).isModule.toSMul z y) hu).trans hy.symm)))

instance tensorProjection_unit_isIso (N : X.Modules) :
    IsIso (tensorProjection f (SheafOfModules.unit _) N) := by
  have h := tensorProjection_unit f N
  have hc : IsIso (tensorProjection f (SheafOfModules.unit _) N ≫
      (tensorProjectionUnitTargetIso f N).hom) :=
    h.symm ▸ (leftUnitIso Y.sheaf ((pushforward f).obj N)).isIso_hom
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _
    (tensorProjectionUnitTargetIso f N).isIso_hom hc

/-- For a trivial line, the projection morphism is an isomorphism. -/
lemma tensorProjection_isIso_of_trivial {L : Y.Modules}
    (e : L ≅ SheafOfModules.unit _) (N : X.Modules) : IsIso (tensorProjection f L N) := by
  have h := tensorProjection_naturality_left f e.hom N
  let e₁ := (tensorLeftIso Y.sheaf e).app ((pushforward f).obj N)
  let e₂ := (pushforward f).mapIso
    ((tensorLeftIso X.sheaf ((Scheme.Modules.pullback f).mapIso e)).app N)
  have h' : e₁.hom ≫ tensorProjection f (SheafOfModules.unit _) N =
      tensorProjection f L N ≫ e₂.hom := h
  have hc : IsIso (e₁.hom ≫ tensorProjection f (SheafOfModules.unit _) N) :=
    IsIso.comp_isIso' e₁.isIso_hom (tensorProjection_unit_isIso f N)
  have hc' : IsIso (tensorProjection f L N ≫ e₂.hom) := h' ▸ hc
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ e₂.isIso_hom hc'

end ActualSheafTensor

end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace ActualSheafTensor
attribute [local instance] projectionSectionModule projectionOpenSectionModule
open Scheme.Modules

/-- Convert an open-subscheme unit trivialization to the exact
slice-site unit trivialization used by the tensor construction. -/
def sliceUnitIso {X : Scheme.{0}} (L : X.Modules) (U : X.Opens)
    (e : (restrictFunctor U.ι).obj L ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    L.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U) :=
  (overEquiv U).functor.preimageIso
    ((overFunctorEquiv U).app L ≪≫ e ≪≫ (restrictUnitIso U.ι).symm ≪≫
      ((overFunctorEquiv U).app (SheafOfModules.unit X.ringCatSheaf)).symm)

/-- The pullback of a line bundle is a line bundle, via
inverse-image trivializing opens and the pullback of the unit. -/
def LineTrivialization.pullback {X Y : Scheme.{0}} (f : X ⟶ Y)
    (L : Y.Modules) (d : LineTrivialization Y.sheaf L) :
    LineTrivialization X.sheaf ((Scheme.Modules.pullback f).obj L) where
  I := d.I
  obj i := f ⁻¹ᵁ d.obj i
  cover := by
    apply (Opens.coversTop_iff X _).mpr
    apply le_antisymm le_top
    intro x _
    have hy : f x ∈ ⨆ i, d.obj i := by
      rw [(Opens.coversTop_iff Y _).mp d.cover]
      trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  iso i := sliceUnitIso _ _
    (((CoherentBaseChange.pullbackRestrictNatIso f (d.obj i)).app L).symm ≪≫
      (Scheme.Modules.pullback (f ∣_ d.obj i)).mapIso (d.schemeIso L i) ≪≫
      sheafPullbackUnitIso (f ∣_ d.obj i))
end ActualSheafTensor

end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
open Scheme.Modules
namespace ActualSheafTensor
attribute [local instance] projectionSectionModule projectionOpenSectionModule
variable {Y : Scheme.{0}} {L K : Y.Modules}

/-- A module-sheaf isomorphism transports a line atlas. -/
def LineTrivialization.ofIso (d : LineTrivialization Y.sheaf L) (e : K ≅ L) :
    LineTrivialization Y.sheaf K where
  I := d.I
  obj := d.obj
  cover := d.cover
  iso j := (SheafOfModules.overFunctor Y.ringCatSheaf (d.obj j)).mapIso e ≪≫ d.iso j

/-- Restriction of a line bundle to any open subscheme. -/
def LineTrivialization.restrict (d : LineTrivialization Y.sheaf L) (U : Y.Opens) :
    LineTrivialization U.toScheme.sheaf ((restrictFunctor U.ι).obj L) :=
  (d.pullback U.ι L).ofIso ((restrictFunctorIsoPullback U.ι).app L)
end ActualSheafTensor

namespace ActualCartier
open ActualSheafTensor
variable {X Y : Scheme.{0}} (g : X ⟶ Y)
  (d : LineTrivialization Y.sheaf (idealSheaf g)) (U : Y.Opens)

/-- The restricted ideal line atlas is induced by the kernel restriction isomorphism. -/
def restrictedLine : LineTrivialization U.toScheme.sheaf (idealSheaf (g ∣_ U)) :=
  (d.restrict U).ofIso (idealRestrictionIso g U).symm
end ActualCartier

end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace ActualOpenSupport
variable {X Y : Scheme.{0}} (g : X ⟶ Y) [IsClosedImmersion g]

/-- The geometric complement of the restricted closed immersion
is precisely the inverse image of its original geometric complement. -/
lemma complement_restrict (U : Y.Opens) :
    complement (g ∣_ U) = U.ι ⁻¹ᵁ complement g := by
  ext y
  change (¬ ∃ x, (g ∣_ U) x = y) ↔ ¬ ∃ x, g x = U.ι y
  constructor
  · intro h ⟨x, hx⟩
    apply h
    have hxU : x ∈ g ⁻¹ᵁ U := by
      change g x ∈ U
      rw [hx]
      exact y.property
    refine ⟨⟨x, hxU⟩, ?_⟩
    apply Subtype.ext
    change g x = y.val at hx
    exact (morphismRestrict_base_coe g U _).trans hx
  · intro h ⟨x, hx⟩
    apply h
    refine ⟨x.val, ?_⟩
    change g x.val = y.val
    exact (morphismRestrict_base_coe g U x).symm.trans (congrArg Subtype.val hx)
end ActualOpenSupport

end

noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace SheafLocality
universe u
variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u}) {ι : Type*} {X : ι → C}

/-- Equality of module-sheaf morphisms descends from any covering family. -/
lemma module_hom_ext_of_coversTop (hX : J.CoversTop X)
    {F G : SheafOfModules.{u} R} {f g : F ⟶ G}
    (h : ∀ i, (SheafOfModules.overFunctor R (X i)).map f =
      (SheafOfModules.overFunctor R (X i)).map g) : f = g := by
  apply (SheafOfModules.toSheaf R).map_injective
  apply hom_ext_of_coversTop hX
  intro i
  exact congrArg ((SheafOfModules.toSheaf (R.over (X i))).map) (h i)

/-- Epimorphisms, as well as monomorphisms, descend from restriction. -/
lemma module_epi_of_coversTop (hX : J.CoversTop X)
    {F G : SheafOfModules.{u} R} (f : F ⟶ G)
    (h : ∀ i, Epi ((SheafOfModules.overFunctor R (X i)).map f)) : Epi f := by
  constructor
  intro H a b hab
  apply module_hom_ext_of_coversTop R hX
  intro i
  have := h i
  apply (cancel_epi ((SheafOfModules.overFunctor R (X i)).map f)).mp
  simpa only [Functor.map_comp] using
    congrArg ((SheafOfModules.overFunctor R (X i)).map) hab

/-- The global isomorphism test on a covering family, for modules. -/
lemma module_isIso_of_coversTop [Balanced (SheafOfModules.{u} R)]
    (hX : J.CoversTop X) {F G : SheafOfModules.{u} R} (f : F ⟶ G)
    (h : ∀ i, IsIso ((SheafOfModules.overFunctor R (X i)).map f)) : IsIso f := by
  have : Mono f := module_mono_of_coversTop R hX f (fun i => by have := h i; infer_instance)
  have : Epi f := module_epi_of_coversTop R hX f (fun i => by have := h i; infer_instance)
  exact isIso_of_mono_of_epi f
end SheafLocality

namespace CoherentGlobal
open Scheme.Modules
/-- Isomorphism of scheme-module morphisms is local on any open cover. -/
lemma isIso_of_restrict_cover {Y : Scheme.{0}} {ι : Type*} (U : ι → Y.Opens)
    (hU : (Opens.grothendieckTopology Y).CoversTop U)
    {M N : Y.Modules} (f : M ⟶ N)
    (h : ∀ i, IsIso ((restrictFunctor (U i).ι).map f)) : IsIso f := by
  apply SheafLocality.module_isIso_of_coversTop Y.ringCatSheaf hU
  intro i
  have := h i
  let e := overFunctorEquiv (U i)
  have hcomp : IsIso (((SheafOfModules.overFunctor Y.ringCatSheaf (U i)) ⋙
      (overEquiv (U i)).functor).map f) :=
    ((NatIso.isIso_map_iff e f).mpr (h i))
  have : IsIso ((overEquiv (U i)).functor.map
      ((SheafOfModules.overFunctor Y.ringCatSheaf (U i)).map f)) := hcomp
  exact isIso_of_reflects_iso
    ((SheafOfModules.overFunctor Y.ringCatSheaf (U i)).map f) (overEquiv (U i)).functor
end CoherentGlobal

end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace SheafLocality
open Scheme.Modules
variable {Y : Scheme.{0}} {ι : Type*} (X : ι → Scheme.{0})
    (f : ∀ i, X i ⟶ Y) [∀ i, IsOpenImmersion (f i)]

/-- Restrictions along an open immersion cover are jointly faithful,
including their non-definitional coefficient-ring changes. -/
lemma module_zero_of_openCover
    (h : (⨆ i, (f i).opensRange) = ⊤)
    {M N : Y.Modules} (a : M ⟶ N)
    (ha : ∀ i, (restrictFunctor (f i)).map a = 0) : a = 0 := by
  apply module_hom_ext_of_coversTop Y.ringCatSheaf
    ((Opens.coversTop_iff Y _).mpr h)
  intro i
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  let W : Y.Opens := V.unop.left
  have hW : W ≤ (f i).opensRange := leOfHom V.unop.hom
  let T := (f i) ⁻¹ᵁ W
  have he : (f i) ''ᵁ T = W := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
    exact inf_eq_right.mpr hW
  have hz : ∀ m : M.val.obj (op ((f i) ''ᵁ T)),
      a.val.app (op ((f i) ''ᵁ T)) m = 0 := by
    intro m
    exact congrArg (fun q => q.val.app (op T) m) (ha i)
  rw [he] at hz
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  exact hz
end SheafLocality

end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualCartier
open CoherentGlobal ActualSheafTensor
variable {X Y : Scheme.{0}} [IsLocallyNoetherian Y]
  (f : X ⟶ Y) [IsClosedImmersion f]
  (d : LineTrivialization Y.sheaf (idealSheaf f))

/-- The ideal resolution in the coherent category. A Cartier
hypothesis here is only local triviality of the closed ideal. -/
abbrev action : coherentTensorLine (idealSheaf f) d ⟶ 𝟭 (Coh Y) :=
  coherentIdealAction (idealSheaf f) d (idealι f)

lemma kernel_app_essImage (M : Coh Y) :
    (cohPushforward f).essImage (kernel ((action f d).app M)) := by
  let K := kernel ((action f d).app M)
  have : K.obj.IsFinitePresentation := K.property
  obtain ⟨N, ⟨e⟩⟩ := exists_coherent_preimage f K.obj
    (congrArg (fun e => e.hom)
      (coherentCartierKernel_annihilated (idealSheaf f) d (idealι f) M))
  exact ⟨N, ⟨ObjectProperty.isoMk _ e⟩⟩

lemma cokernel_app_essImage (M : Coh Y) :
    (cohPushforward f).essImage (cokernel ((action f d).app M)) := by
  let Q := cokernel ((action f d).app M)
  have : Q.obj.IsFinitePresentation := Q.property
  obtain ⟨N, ⟨e⟩⟩ := exists_coherent_preimage f Q.obj
    (congrArg (fun e => e.hom)
      (coherentCartierCokernel_annihilated (idealSheaf f) d (idealι f) M))
  exact ⟨N, ⟨ObjectProperty.isoMk _ e⟩⟩

lemma kernel_functor_essImage (M : Coh Y) :
    (cohPushforward f).essImage ((kernel (action f d)).obj M) := by
  obtain ⟨N, ⟨e⟩⟩ := kernel_app_essImage f d M
  exact ⟨N, ⟨e ≪≫ (PreservesKernel.iso ((evaluation (Coh Y) (Coh Y)).obj M)
    (action f d)).symm⟩⟩

lemma cokernel_functor_essImage (M : Coh Y) :
    (cohPushforward f).essImage ((cokernel (action f d)).obj M) := by
  obtain ⟨N, ⟨e⟩⟩ := cokernel_app_essImage f d M
  exact ⟨N, ⟨e ≪≫ (PreservesCokernel.iso ((evaluation (Coh Y) (Coh Y)).obj M)
    (action f d)).symm⟩⟩

/-- First Cartier Tor, as a functor to coherent sheaves ON the divisor. -/
def firstTor : Coh Y ⥤ Coh X :=
  Functor.essImage.liftFunctor (kernel (action f d)) (cohPushforward f)
    (kernel_functor_essImage f d)
/-- Ordinary Cartier restriction on coherent sheaves. -/
def restriction : Coh Y ⥤ Coh X :=
  Functor.essImage.liftFunctor (cokernel (action f d)) (cohPushforward f)
    (cokernel_functor_essImage f d)

def firstTorPushforwardIso : firstTor f d ⋙ cohPushforward f ≅ kernel (action f d) :=
  Functor.essImage.liftFunctorCompIso (kernel (action f d)) (cohPushforward f)
    (kernel_functor_essImage f d)
def restrictionPushforwardIso : restriction f d ⋙ cohPushforward f ≅ cokernel (action f d) :=
  Functor.essImage.liftFunctorCompIso (cokernel (action f d)) (cohPushforward f)
    (cokernel_functor_essImage f d)
end ActualCartier

end

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CoherentK0
universe v w u₁ u₂ u₃
variable {C : Type u₁} [Category.{v} C] [Preadditive C]
  {D : Type u₂} [Category.{w} D] [Abelian D]

/-- Pointwise kernels of transformations of additive functors are additive. -/
lemma kernel_functor_additive (F G : C ⥤ D) [F.Additive] [G.Additive] (a : F ⟶ G) :
    (kernel a).Additive where
  map_add {X Y p q} := by
    have : Mono ((kernel.ι a).app Y) := inferInstance
    apply (cancel_mono ((kernel.ι a).app Y)).mp
    simp only [NatTrans.naturality, F.map_add, Preadditive.add_comp, Preadditive.comp_add]

/-- The corresponding cokernel statement. -/
lemma cokernel_functor_additive (F G : C ⥤ D) [F.Additive] [G.Additive] (a : F ⟶ G) :
    (cokernel a).Additive where
  map_add {X Y p q} := by
    have : Epi ((cokernel.π a).app X) := inferInstance
    apply (cancel_epi ((cokernel.π a).app X)).mp
    simp only [← NatTrans.naturality, G.map_add, Preadditive.add_comp, Preadditive.comp_add]

end CoherentK0

namespace CoherentK0
universe v₁ v₂ u₁ u₂
variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]
/-- Once kernel and cokernel functors have been descended along a
fully faithful exact inclusion, their universal properties imply
Cartier additivity in the target's Grothendieck group. -/
lemma cartier_from_functor_kernels
    (J : D ⥤ C) [J.Full] [J.Faithful] [J.Additive]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    (T : C ⥤ C) [T.Additive]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (a : T ⟶ 𝟭 C) (K Q : C ⥤ D)
    (eK : K ⋙ J ≅ kernel a) (eQ : Q ⋙ J ≅ cokernel a)
    {S : ShortComplex C} (hS : S.ShortExact) :
    cls (Q.obj S.X₂) - cls (K.obj S.X₂) =
      (cls (Q.obj S.X₁) - cls (K.obj S.X₁)) +
      (cls (Q.obj S.X₃) - cls (K.obj S.X₃)) := by
  have : (kernel a).Additive := kernel_functor_additive T (𝟭 C) a
  have : (cokernel a).Additive := cokernel_functor_additive T (𝟭 C) a
  have : (K ⋙ J).Additive := Functor.additive_of_iso eK.symm
  have : (Q ⋙ J).Additive := Functor.additive_of_iso eQ.symm
  have : K.Additive := Functor.additive_of_comp_faithful K J
  have : Q.Additive := Functor.additive_of_comp_faithful Q J
  let k : K ⋙ J ⟶ T := eK.hom ≫ kernel.ι a
  let q : 𝟭 C ⟶ Q ⋙ J := cokernel.π a ≫ eQ.inv
  have zk : k ≫ a = 0 := by simp [k]
  have zq : a ≫ q = 0 := by simp [q, ← Category.assoc]
  have hk (X : C) : IsLimit (KernelFork.ofι (k.app X) (NatTrans.congr_app zk X)) := by
    let E := (evaluation C C).obj X
    have h := isLimitOfHasKernelOfPreservesLimit E a
    apply IsLimit.ofIsoLimit h
    refine Fork.ext (eK.app X).symm ?_
    dsimp [k]
    simp
    rfl
  have hq (X : C) : IsColimit (CokernelCofork.ofπ (q.app X) (NatTrans.congr_app zq X)) := by
    let E := (evaluation C C).obj X
    have h := isColimitOfHasCokernelOfPreservesColimit E a
    apply IsColimit.ofIsoColimit h
    refine Cofork.ext (eQ.app X).symm ?_
    rfl
  exact cartier_restriction_additive J T K Q k a q zk zq hk hq hS
end CoherentK0

end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace ActualCartier
open CoherentGlobal ActualSheafTensor CoherentK0
variable {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  (f : X ⟶ Y) [IsClosedImmersion f]
  (d : LineTrivialization Y.sheaf (idealSheaf f))

/-- Cartier restriction minus first Tor is additive on coherent
sheaves, with values in the coherent Grothendieck group ON the divisor. -/
lemma derivedRestriction_additive {S : ShortComplex (Coh Y)} (hS : S.ShortExact) :
    cls ((restriction f d).obj S.X₂) - cls ((firstTor f d).obj S.X₂) =
      (cls ((restriction f d).obj S.X₁) - cls ((firstTor f d).obj S.X₁)) +
      (cls ((restriction f d).obj S.X₃) - cls ((firstTor f d).obj S.X₃)) := by
  let T := coherentTensorLine (idealSheaf f) d
  have : PreservesFiniteLimits T := T.preservesFiniteLimits_of_preservesHomology
  have : PreservesFiniteColimits T := T.preservesFiniteColimits_of_preservesHomology
  exact cartier_from_functor_kernels (cohPushforward f) T (action f d)
    (firstTor f d) (restriction f d) (firstTorPushforwardIso f d)
    (restrictionPushforwardIso f d) hS

/-- The derived restriction homomorphism on the coherent Grothendieck group. -/
def derivedRestriction : CoherentK0.Group (Coh Y) →+ CoherentK0.Group (Coh X) :=
  CoherentK0.lift
    (fun M => cls ((restriction f d).obj M) - cls ((firstTor f d).obj M))
    (fun e => by rw [cls_iso ((restriction f d).mapIso e),
      cls_iso ((firstTor f d).mapIso e)])
    (derivedRestriction_additive f d)

@[simp] lemma derivedRestriction_cls (M : Coh Y) :
    derivedRestriction f d (cls M) =
      cls ((restriction f d).obj M) - cls ((firstTor f d).obj M) :=
  CoherentK0.lift_cls
    (fun N => cls ((restriction f d).obj N) - cls ((firstTor f d).obj N))
    (fun e => by rw [cls_iso ((restriction f d).mapIso e),
      cls_iso ((firstTor f d).mapIso e)]) (derivedRestriction_additive f d) M

/-- The finite coherent-filtration identity used for the nilpotent quotient
in the Cartier restriction formula, before identifying the individual supported
first-Tor terms with the conormal twist. -/
lemma derivedRestriction_filtered {M : Coh Y} {qs : List (Coh Y)}
    (h : FilteredBy M qs) :
    cls ((restriction f d).obj M) - cls ((firstTor f d).obj M) =
      (qs.map fun Q => cls ((restriction f d).obj Q) - cls ((firstTor f d).obj Q)).sum := by
  simpa only [derivedRestriction_cls] using map_cls_filteredBy (derivedRestriction f d) h
end ActualCartier

end

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualSheafTensor
attribute [local instance] projectionSectionModule projectionOpenSectionModule
universe u
variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
local instance : MonoidalCategory (PresheafOfModules.{u} (ringSheaf R).obj) :=
  inferInstanceAs (MonoidalCategory (PresheafOfModules.{u}
    (R.obj ⋙ forget₂ CommRingCat RingCat)))

private local instance unitSectionSMul (M : SheafOfModules.{u} (ringSheaf R))
    (U : Cᵒᵖ) : SMul ((SheafOfModules.unit (ringSheaf R)).val.obj U) (M.val.obj U) :=
  show SMul (R.obj.obj U) (M.val.obj U) from (M.val.obj U).isModule.toSMul

lemma idealAction_zero_of_sections {L : SheafOfModules.{u} (ringSheaf R)}
    (i : L ⟶ SheafOfModules.unit _) (M : SheafOfModules.{u} (ringSheaf R))
    (h : ∀ (U : Cᵒᵖ) (l : L.val.obj U) (m : M.val.obj U), (i.val.app U l) • m = 0) :
    (idealAction R i).app M = 0 := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)
  apply (adj.homEquiv _ _).injective
  rw [idealAction_adjoint]
  erw [Adjunction.homEquiv_unit]
  change (i.val ▷ M.val) ≫ (λ_ M.val).hom = 0
  apply PresheafOfModules.hom_ext
  intro U
  let A := (L.val ⊗ M.val).obj U
  let B := M.val.obj U
  let a : A ⟶ B := ((i.val ▷ M.val) ≫ (λ_ M.val).hom).app U
  let b : A ⟶ B := 0
  change a = b
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul l m => exact h U l m
  | add x y hx hy =>
    exact (a.hom.map_add x y).trans
      ((congrArg₂ (· + ·) hx hy).trans (b.hom.map_add x y).symm)

end ActualSheafTensor

namespace ActualCartier
variable {X Y : Scheme.{0}} (f : X ⟶ Y)
lemma ideal_section_killed (U : Y.Opens) (l : (idealSheaf f).val.obj (op U)) :
    f.app U ((idealι f).val.app (op U) l) = 0 := by
  exact congrArg (fun g : idealSheaf f ⟶
    (Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf) =>
      g.val.app (op U) l) (kernel.condition (structureMap f))

/-- The closed ideal acts by zero on every sheaf pushed forward from
that subscheme. This is a direct calculation with the scheme comorphism. -/
lemma idealAction_pushforward_zero (N : X.Modules) :
    (ActualSheafTensor.idealAction Y.sheaf (idealι f)).app
      ((Scheme.Modules.pushforward f).obj N) = 0 := by
  apply ActualSheafTensor.idealAction_zero_of_sections
  intro U l m
  change (N.smul (f.app U.unop ((idealι f).val.app U l)) :
    Γ(N, f ⁻¹ᵁ U.unop) ⟶ Γ(N, f ⁻¹ᵁ U.unop)).hom m = 0
  rw [ideal_section_killed f U.unop l, map_zero]
  rfl
end ActualCartier

end

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CartierUniversal
universe v₁ v₂ u₁ u₂
variable {C : Type u₁} [Category.{v₁} C] [HasZeroMorphisms C]
  {D : Type u₂} [Category.{v₂} D]
  {L : C ⥤ D} {J : D ⥤ C} (adj : L ⊣ J) [J.Full] [J.Faithful]
  {E M : C} {Q : D} (a : E ⟶ M) (q : M ⟶ J.obj Q) (z : a ≫ q = 0)
  (hq : IsColimit (CokernelCofork.ofπ q z))
  (hu : a ≫ adj.unit.app M = 0)

/-- The reflection unit identifies the descended cokernel with geometric pullback. -/
def pullbackIso : L.obj M ≅ Q := by
  have hdesc : q ≫ hq.desc (CokernelCofork.ofπ (adj.unit.app M) hu) = adj.unit.app M :=
    Cofork.IsColimit.π_desc hq
  let p : Q ⟶ L.obj M := J.preimage (hq.desc (CokernelCofork.ofπ (adj.unit.app M) hu))
  have hp : q ≫ J.map p = adj.unit.app M := by simpa [p] using hdesc
  let t : L.obj M ⟶ Q := (adj.homEquiv M Q).symm q
  have ht : adj.unit.app M ≫ J.map t = q := by
    exact (adj.homEquiv M Q).apply_symm_apply q
  refine ⟨t, p, ?_, ?_⟩
  · apply (adj.homEquiv M (L.obj M)).injective
    rw [adj.homEquiv_naturality_right, Equiv.apply_symm_apply, hp]
    simp [Adjunction.homEquiv_unit]
  · apply J.map_injective
    apply Cofork.IsColimit.hom_ext hq
    change q ≫ J.map (p ≫ t) = q ≫ J.map (𝟙 Q)
    rw [J.map_comp, J.map_id, ← Category.assoc, hp, ht, Category.comp_id]
end CartierUniversal

end

end OAI
