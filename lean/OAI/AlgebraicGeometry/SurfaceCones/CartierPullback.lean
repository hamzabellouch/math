import OAI.AlgebraicGeometry.SurfaceCones.GeometricChartSandwich

namespace OAI

private local instance coherentSectionModule (X : AlgebraicGeometry.Scheme.{0})
    (M : CoherentGlobal.Coh X) (U : X.Opensᵒᵖ) :
    Module (X.sheaf.obj.obj U) (M.obj.val.obj U) :=
  (M.obj.val.obj U).isModule

private theorem kernelMono {C : Type*} [CategoryTheory.Category C]
    [CategoryTheory.Limits.HasZeroMorphisms C] {A B : C} (g : A ⟶ B)
    [CategoryTheory.Limits.HasKernel g] : CategoryTheory.Mono (CategoryTheory.Limits.kernel.ι g) :=
  CategoryTheory.Limits.equalizer.ι_mono

private theorem counitIsIso {C D : Type*} [CategoryTheory.Category C]
    [CategoryTheory.Category D] {L : CategoryTheory.Functor C D} {R : CategoryTheory.Functor D C}
    (adj : CategoryTheory.Adjunction L R) [R.Full] [R.Faithful] (N : D) :
    CategoryTheory.IsIso (adj.counit.app N) := inferInstance

/-!
# Cartier pullback and coherent lattice filtrations

This development accompanies *A Complete Local Domain without a Small
Cohen–Macaulay Module* (OpenAI, 2026).
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace ActualCartier
open CoherentGlobal ActualSheafTensor Scheme.Modules
variable {X Y : Scheme.{0}} [IsLocallyNoetherian Y]
  (f : X ⟶ Y) [IsClosedImmersion f]
  (d : LineTrivialization Y.sheaf (idealSheaf f))

def restrictionUnit : 𝟭 (Coh Y) ⟶ restriction f d ⋙ cohPushforward f :=
  cokernel.π (action f d) ≫ (restrictionPushforwardIso f d).inv

lemma restrictionUnit_zero : action f d ≫ restrictionUnit f d = 0 := by
  simp [restrictionUnit, ← Category.assoc]

/-- This is the cokernel fork in all sheaves of modules after
forgetting coherence. -/
def restrictionUnitIsColimit (M : Coh Y) :
    IsColimit (CokernelCofork.ofπ ((restrictionUnit f d).app M).hom
      (show ((action f d).app M).hom ≫ ((restrictionUnit f d).app M).hom = 0 from
        congrArg (fun z => z.hom) (NatTrans.congr_app (restrictionUnit_zero f d) M))) := by
  let E := (evaluation (Coh Y) (Coh Y)).obj M ⋙ cohInclusion Y
  have h := isColimitOfHasCokernelOfPreservesColimit E (action f d)
  apply IsColimit.ofIsoColimit h
  refine Cofork.ext ((cohInclusion Y).mapIso ((restrictionPushforwardIso f d).app M)).symm ?_
  rfl

/-- The descended ordinary restriction is the geometric pullback.
This spells out its universal property, rather than using the desired
identification as an extra hypothesis. -/
def restrictionPullbackIso (M : Coh Y) :
    (Scheme.Modules.pullback f).obj M.obj ≅ ((restriction f d).obj M).obj := by
  let a : (tensor Y.sheaf (idealSheaf f) M.obj : Y.Modules) ⟶ M.obj :=
    (idealAction Y.sheaf (idealι f)).app M.obj
  let q : M.obj ⟶ (pushforward f).obj (((restriction f d).obj M).obj) :=
    ((restrictionUnit f d).app M).hom
  have z : a ≫ q = ⟨0⟩ :=
    congrArg (fun z => z.hom) (NatTrans.congr_app (restrictionUnit_zero f d) M)
  let adj := pullbackPushforwardAdjunction f
  have hu : a ≫ (show M.obj ⟶
      (pushforward f).obj ((Scheme.Modules.pullback f).obj M.obj) from adj.unit.app M.obj) = ⟨0⟩ := by
    have h := (idealAction Y.sheaf (idealι f)).naturality (adj.unit.app M.obj)
    have hz : (idealAction Y.sheaf (idealι f)).app
        ((pushforward f).obj ((Scheme.Modules.pullback f).obj M.obj)) = 0 :=
      idealAction_pushforward_zero f ((Scheme.Modules.pullback f).obj M.obj)
    erw [hz, comp_zero] at h
    exact h.symm
  exact CartierUniversal.pullbackIso adj a q z (restrictionUnitIsColimit f d M) hu

include d in
lemma coherent_pullback (M : Coh Y) : ((Scheme.Modules.pullback f).obj M.obj).IsFinitePresentation :=
  (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso
    (restrictionPullbackIso f d M).symm ((restriction f d).obj M).property
end ActualCartier

end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualCartier
open CoherentGlobal ActualSheafTensor CoherentK0
variable {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  (f : X ⟶ Y) [IsClosedImmersion f]
  (d : LineTrivialization Y.sheaf (idealSheaf f))

omit [IsLocallyNoetherian X] in
/-- The first Cartier Tor vanishes for a sectionwise torsion-free
coherent sheaf: this is proved from the invertible ideal action. -/
lemma firstTor_isZero (M : Coh Y)
    (hM : ∀ U, Module.IsTorsionFree (Y.sheaf.obj.obj U) (M.obj.val.obj U)) :
    IsZero ((firstTor f d).obj M) := by
  have hmono : Mono (idealι f) :=
    kernelMono (C := SheafOfModules Y.ringCatSheaf) (structureMap f)
  have : Mono ((idealAction Y.sheaf (idealι f)).app M.obj) :=
    @idealAction_mono_of_line _ _ _ Y.sheaf _ _ _ _ (idealSheaf f) d (idealι f) hmono M.obj hM
  have : Mono ((action f d).app M) :=
    (cohInclusion Y).mono_of_mono_map (f := (action f d).app M) (by assumption)
  let e := (firstTorPushforwardIso f d).app M ≪≫
    PreservesKernel.iso ((evaluation (Coh Y) (Coh Y)).obj M) (action f d)
  have hz := (isZero_kernel_of_mono ((action f d).app M)).of_iso e
  apply (IsZero.iff_id_eq_zero _).mpr
  apply (cohPushforward f).zero_of_map_zero
  rw [(cohPushforward f).map_id]
  exact hz.eq_of_src _ _

lemma derivedRestriction_cls_torsionFree (M : Coh Y)
    (hM : ∀ U, Module.IsTorsionFree (Y.sheaf.obj.obj U) (M.obj.val.obj U)) :
    derivedRestriction f d (cls M) = cls ((restriction f d).obj M) := by
  rw [derivedRestriction_cls, cls_isZero (firstTor_isZero f d M hM), sub_zero]

omit [IsLocallyNoetherian X] in
/-- A coherent sheaf pushed forward from the divisor has zero Cartier action. -/
lemma action_pushforward_zero (N : Coh X) :
    (action f d).app ((cohPushforward f).obj N) = 0 := by
  apply ObjectProperty.hom_ext
  exact idealAction_pushforward_zero f N.obj

/-- The first Tor of a supported layer is the ambient ideal line tensor
after closed pushforward. Full faithfulness descends this identification to the divisor. -/
def firstTor_supported_pushforwardIso (N : Coh X) :
    (cohPushforward f).obj ((firstTor f d).obj ((cohPushforward f).obj N)) ≅
      (coherentTensorLine (idealSheaf f) d).obj ((cohPushforward f).obj N) :=
  (firstTorPushforwardIso f d).app ((cohPushforward f).obj N) ≪≫
    PreservesKernel.iso ((evaluation (Coh Y) (Coh Y)).obj ((cohPushforward f).obj N))
      (action f d) ≪≫
    kernelIsoOfEq (action_pushforward_zero f d N) ≪≫ kernelZeroIsoSource

/-- Ordinary restriction of a closed pushforward is the original
coherent sheaf on the divisor. -/
def restriction_supported_iso (N : Coh X) :
    (restriction f d).obj ((cohPushforward f).obj N) ≅ N :=
  ObjectProperty.isoMk _ ((restrictionPullbackIso f d ((cohPushforward f).obj N)).symm ≪≫
    @asIso _ _ _ _ ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app N.obj)
      (counitIsIso (Scheme.Modules.pullbackPushforwardAdjunction f) N.obj))

lemma derivedRestriction_supported (N : Coh X) :
    derivedRestriction f d (cls ((cohPushforward f).obj N)) =
      cls N - cls ((firstTor f d).obj ((cohPushforward f).obj N)) := by
  rw [derivedRestriction_cls, cls_iso (restriction_supported_iso f d N)]
end ActualCartier

end

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
open scoped TensorProduct
namespace ActualSheafTensor
open Scheme.Modules
variable (X : Scheme.{0}) (U : X.Opens)

/-- The inverse restriction comparison is the identity on pure sections,
with the scalar action transported by the open immersion's ring isomorphism. -/
lemma tensorSchemeRestrictIso_inv_pure (M N : X.Modules) (V : U.toScheme.Opens)
    (x : ((restrictFunctor U.ι).obj M).val.obj (op V))
    (y : ((restrictFunctor U.ι).obj N).val.obj (op V)) :
    (tensorSchemeRestrictIso X U M N).inv.val.app (op V)
      (pure U.toScheme.sheaf ((restrictFunctor U.ι).obj M)
        ((restrictFunctor U.ι).obj N) (op V) x y) =
    pure X.sheaf M N (op (U.ι ''ᵁ V)) x y := by
  let P := PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.sheaf.obj) M.val N.val
  let e := schemePresheafTensorRestrictIso X U M.val N.val
  let sh := PresheafOfModules.sheafification (𝟙 U.toScheme.ringCatSheaf.obj)
  let η := (PresheafOfModules.sheafificationAdjunction
    (𝟙 U.toScheme.ringCatSheaf.obj)).unit
  have hn := η.naturality e.inv
  have hc := ModuleSheafification.comparison_unit U.ι.opensFunctor
    (schemeRingRestrictHom X U) P
  have hn' := congrArg (fun g => g.app (op V)
      (x ⊗ₜ[U.toScheme.sheaf.obj.obj (op V)] y)) hn
  have hc' := congrArg (fun g => g.app (op V)
      (x ⊗ₜ[X.sheaf.obj.obj (op (U.ι ''ᵁ V))] y)) hc
  change (schemeSheafifyRestrictMap X U P).val.app (op V)
    ((sh.map e.inv).val.app (op V)
      (pure U.toScheme.sheaf ((restrictFunctor U.ι).obj M)
        ((restrictFunctor U.ι).obj N) (op V) x y)) = _
  change (η.app ((schemePresheafRestrict X U).obj P)).app (op V)
      (x ⊗ₜ[X.sheaf.obj.obj (op (U.ι ''ᵁ V))] y) =
    (sh.map e.inv).val.app (op V)
      (pure U.toScheme.sheaf ((restrictFunctor U.ι).obj M)
        ((restrictFunctor U.ι).obj N) (op V) x y) at hn'
  change (schemeSheafifyRestrictMap X U P).val.app (op V)
      ((η.app ((schemePresheafRestrict X U).obj P)).app (op V)
        (x ⊗ₜ[X.sheaf.obj.obj (op (U.ι ''ᵁ V))] y)) =
    pure X.sheaf M N (op (U.ι ''ᵁ V)) x y at hc'
  exact (congrArg ((schemeSheafifyRestrictMap X U P).val.app (op V)) hn'.symm).trans hc'
end ActualSheafTensor

end

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped TensorProduct
namespace ActualSheafTensor
universe u
variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
local instance : MonoidalCategory (PresheafOfModules.{u} (ringSheaf R).obj) :=
  inferInstanceAs (MonoidalCategory (PresheafOfModules.{u}
    (R.obj ⋙ forget₂ CommRingCat RingCat)))

lemma tensorLeft_map_pure (M : SheafOfModules.{u} (ringSheaf R))
    {N N' : SheafOfModules.{u} (ringSheaf R)} (g : N ⟶ N')
    (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) :
    ((tensorLeft R M).map g).val.app U (pure R M N U x y) =
      pure R M N' U x (g.val.app U y) := by
  have h := (PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit.naturality
    (M.val ◁ g.val)
  exact (congrArg (fun k => k.app U (x ⊗ₜ[R.obj.obj U] y)) h).symm

lemma pure_naturality (M N : SheafOfModules.{u} (ringSheaf R))
    {U V : Cᵒᵖ} (g : U ⟶ V) (x : M.val.obj U) (y : N.val.obj U) :
    (tensor R M N).val.map g (pure R M N U x y) =
      pure R M N V (M.val.map g x) (N.val.map g y) := by
  let P := PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := R.obj) M.val N.val
  let η := (PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit.app P
  exact (PresheafOfModules.naturality_apply η g (x ⊗ₜ[R.obj.obj U] y)).symm
end ActualSheafTensor

end

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
open scoped TensorProduct
namespace ActualSheafTensor
open Scheme.Modules CoherentBaseChange
variable {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens) (L : Y.Modules) (N : X.Modules)

def projectionRestrictLeft :
    tensor U.toScheme.sheaf ((restrictFunctor U.ι).obj L)
      ((restrictFunctor U.ι).obj ((pushforward f).obj N)) ⟶
    (pushforward (f ∣_ U)).obj ((restrictFunctor (f ⁻¹ᵁ U).ι).obj
      (tensor X.sheaf ((Scheme.Modules.pullback f).obj L) N)) := by
  exact (tensorSchemeRestrictIso Y U L ((pushforward f).obj N)).inv ≫
    (restrictFunctor U.ι).map (tensorProjection f L N) ≫
    (pushforwardRestrictNatIso f U).hom.app
      (tensor X.sheaf ((Scheme.Modules.pullback f).obj L) N)

def projectionRestrictRight :
    tensor U.toScheme.sheaf ((restrictFunctor U.ι).obj L)
      ((restrictFunctor U.ι).obj ((pushforward f).obj N)) ⟶
    (pushforward (f ∣_ U)).obj ((restrictFunctor (f ⁻¹ᵁ U).ι).obj
      (tensor X.sheaf ((Scheme.Modules.pullback f).obj L) N)) := by
  let L' := (restrictFunctor U.ι).obj L
  let N' := (restrictFunctor (f ⁻¹ᵁ U).ι).obj N
  let a := (tensorLeft U.toScheme.sheaf L').map
    ((pushforwardRestrictNatIso f U).hom.app N)
  let b := tensorProjection (f ∣_ U) L' N'
  let c := (pushforward (f ∣_ U)).map
    ((tensorLeftMap (f ⁻¹ᵁ U).toScheme.sheaf
      ((pullbackRestrictNatIso f U).hom.app L)).app N')
  let e := (pushforward (f ∣_ U)).map
    (tensorSchemeRestrictIso X (f ⁻¹ᵁ U) ((Scheme.Modules.pullback f).obj L) N).inv
  exact a ≫ b ≫ c ≫ e

lemma projectionRestrictLeft_pure (V : U.toScheme.Opens)
    (x : ((restrictFunctor U.ι).obj L).val.obj (op V))
    (y : ((restrictFunctor U.ι).obj ((pushforward f).obj N)).val.obj (op V)) :
    (projectionRestrictLeft f U L N).val.app (op V)
      (pure U.toScheme.sheaf ((restrictFunctor U.ι).obj L)
        ((restrictFunctor U.ι).obj ((pushforward f).obj N)) (op V) x y) =
    pure X.sheaf ((Scheme.Modules.pullback f).obj L) N
      (op ((f ⁻¹ᵁ U).ι ''ᵁ ((f ∣_ U) ⁻¹ᵁ V)))
      (((Scheme.Modules.pullback f).obj L).val.map
        (eqToHom (image_morphismRestrict_preimage f U V)).op
        (((pullbackPushforwardAdjunction f).unit.app L).val.app (op (U.ι ''ᵁ V)) x))
      (N.val.map (eqToHom (image_morphismRestrict_preimage f U V)).op y) := by
  let T := tensor X.sheaf ((Scheme.Modules.pullback f).obj L) N
  let a := (eqToHom (image_morphismRestrict_preimage f U V)).op
  change T.val.map a
      ((tensorProjection f L N).val.app (op (U.ι ''ᵁ V))
        ((tensorSchemeRestrictIso Y U L ((pushforward f).obj N)).inv.val.app (op V)
          (pure U.toScheme.sheaf ((restrictFunctor U.ι).obj L)
            ((restrictFunctor U.ι).obj ((pushforward f).obj N)) (op V) x y))) = _
  have h₁ := tensorSchemeRestrictIso_inv_pure Y U L ((pushforward f).obj N) V x y
  have h₂ := tensorProjection_pure' f L N (U.ι ''ᵁ V) x y
  exact (congrArg (fun z => T.val.map a
    ((tensorProjection f L N).val.app (op (U.ι ''ᵁ V)) z)) h₁).trans
      ((congrArg (T.val.map a) h₂).trans
        (pure_naturality X.sheaf ((Scheme.Modules.pullback f).obj L) N a _ y))

lemma projectionRestrictRight_pure (V : U.toScheme.Opens)
    (x : ((restrictFunctor U.ι).obj L).val.obj (op V))
    (y : ((restrictFunctor U.ι).obj ((pushforward f).obj N)).val.obj (op V)) :
    (projectionRestrictRight f U L N).val.app (op V)
      (pure U.toScheme.sheaf ((restrictFunctor U.ι).obj L)
        ((restrictFunctor U.ι).obj ((pushforward f).obj N)) (op V) x y) =
    pure X.sheaf ((Scheme.Modules.pullback f).obj L) N
      (op ((f ⁻¹ᵁ U).ι ''ᵁ ((f ∣_ U) ⁻¹ᵁ V)))
      (((pullbackRestrictNatIso f U).hom.app L).val.app (op ((f ∣_ U) ⁻¹ᵁ V))
        (((pullbackPushforwardAdjunction (f ∣_ U)).unit.app
          ((restrictFunctor U.ι).obj L)).val.app (op V) x))
      (N.val.map (eqToHom (image_morphismRestrict_preimage f U V)).op y) := by
  let L' := (restrictFunctor U.ι).obj L
  let N' := (restrictFunctor (f ⁻¹ᵁ U).ι).obj N
  let y' := ((pushforwardRestrictNatIso f U).hom.app N).val.app (op V) y
  let x' := ((pullbackPushforwardAdjunction (f ∣_ U)).unit.app L').val.app (op V) x
  let a := (tensorLeft U.toScheme.sheaf L').map ((pushforwardRestrictNatIso f U).hom.app N)
  let b := tensorProjection (f ∣_ U) L' N'
  let c := (tensorLeftMap (f ⁻¹ᵁ U).toScheme.sheaf
    ((pullbackRestrictNatIso f U).hom.app L)).app N'
  let e := (tensorSchemeRestrictIso X (f ⁻¹ᵁ U) ((Scheme.Modules.pullback f).obj L) N).inv
  have h₁ := tensorLeft_map_pure U.toScheme.sheaf L'
    ((pushforwardRestrictNatIso f U).hom.app N) (op V) x y
  have h₂ := tensorProjection_pure' (f ∣_ U) L' N' V x y'
  have h₃ := tensorLeftMap_pure (f ⁻¹ᵁ U).toScheme.sheaf
    ((pullbackRestrictNatIso f U).hom.app L) N' (op ((f ∣_ U) ⁻¹ᵁ V)) x' y'
  have h₄ := tensorSchemeRestrictIso_inv_pure X (f ⁻¹ᵁ U)
    ((Scheme.Modules.pullback f).obj L) N ((f ∣_ U) ⁻¹ᵁ V)
    (((pullbackRestrictNatIso f U).hom.app L).val.app (op ((f ∣_ U) ⁻¹ᵁ V)) x') y'
  exact (congrArg (fun z => e.val.app (op ((f ∣_ U) ⁻¹ᵁ V))
      (c.val.app (op ((f ∣_ U) ⁻¹ᵁ V)) (b.val.app (op V) z))) h₁).trans
    ((congrArg (fun z => e.val.app (op ((f ∣_ U) ⁻¹ᵁ V))
      (c.val.app (op ((f ∣_ U) ⁻¹ᵁ V)) z)) h₂).trans
    ((congrArg (e.val.app (op ((f ∣_ U) ⁻¹ᵁ V))) h₃).trans h₄))

/-- The tensor projection morphism commutes with open restriction
through the pullback comparison induced by the adjunction. -/
lemma tensorProjection_restrict :
    projectionRestrictLeft f U L N = projectionRestrictRight f U L N := by
  apply tensor_hom_ext U.toScheme.sheaf
  intro V x y
  have hu := unit_mateEquiv_symm (pullbackPushforwardAdjunction f)
    (pullbackPushforwardAdjunction (f ∣_ U)) (restrictSquare f U) L
  have hu' := congrArg (fun g => g.val.app V x) hu
  exact (projectionRestrictLeft_pure f U L N V.unop x y).trans
    ((congrArg (fun z => pure X.sheaf ((Scheme.Modules.pullback f).obj L) N
      (op ((f ⁻¹ᵁ U).ι ''ᵁ ((f ∣_ U) ⁻¹ᵁ V.unop))) z
      (N.val.map (eqToHom (image_morphismRestrict_preimage f U V.unop)).op y)) hu').trans
    (projectionRestrictRight_pure f U L N V.unop x y).symm)
end ActualSheafTensor

end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace ActualSheafTensor
open Scheme.Modules CoherentBaseChange
variable {X Y : Scheme.{0}} (f : X ⟶ Y) (L : Y.Modules)

lemma projectionRestrictRight_isIso (U : Y.Opens)
    (e : (restrictFunctor U.ι).obj L ≅ SheafOfModules.unit _) (N : X.Modules) :
    IsIso (projectionRestrictRight f U L N) := by
  have := tensorProjection_isIso_of_trivial (f ∣_ U) e
    ((restrictFunctor (f ⁻¹ᵁ U).ι).obj N)
  let V := f ⁻¹ᵁ U
  let L' := (restrictFunctor U.ι).obj L
  let N' := (restrictFunctor V.ι).obj N
  let a := (tensorLeft U.toScheme.sheaf L').map
    ((pushforwardRestrictNatIso f U).hom.app N)
  let b := tensorProjection (f ∣_ U) L' N'
  let c₀ := (tensorLeftMap V.toScheme.sheaf
    ((pullbackRestrictNatIso f U).hom.app L)).app N'
  have hc₀ : IsIso c₀ := inferInstanceAs (IsIso
    (((tensorLeftIso V.toScheme.sheaf ((pullbackRestrictNatIso f U).app L)).app N').hom))
  let c := (pushforward (f ∣_ U)).map c₀
  let e' := (pushforward (f ∣_ U)).map
    (tensorSchemeRestrictIso X V ((Scheme.Modules.pullback f).obj L) N).inv
  have ha : IsIso a := inferInstanceAs (IsIso
    (((tensorLeft U.toScheme.sheaf L').mapIso ((pushforwardRestrictNatIso f U).app N)).hom))
  have hb : IsIso b := ‹IsIso (tensorProjection (f ∣_ U) L' N')›
  have hc : IsIso c := @Functor.map_isIso _ _ _ _ _ _ (pushforward (f ∣_ U)) c₀ hc₀
  have he' : IsIso e' := inferInstanceAs (IsIso
    (((pushforward (f ∣_ U)).mapIso
      (tensorSchemeRestrictIso X V ((Scheme.Modules.pullback f).obj L) N).symm).hom))
  change IsIso (a ≫ b ≫ c ≫ e')
  exact IsIso.comp_isIso' ha (IsIso.comp_isIso' hb (IsIso.comp_isIso' hc he'))

lemma projectionRestrict_isIso (U : Y.Opens)
    (e : (restrictFunctor U.ι).obj L ≅ SheafOfModules.unit _) (N : X.Modules) :
    IsIso ((restrictFunctor U.ι).map (tensorProjection f L N)) := by
  have : IsIso (projectionRestrictRight f U L N) := projectionRestrictRight_isIso f L U e N
  have : IsIso (projectionRestrictLeft f U L N) :=
    (tensorProjection_restrict f U L N).symm ▸ inferInstance
  let a := (tensorSchemeRestrictIso Y U L ((pushforward f).obj N)).inv
  let b := (restrictFunctor U.ι).map (tensorProjection f L N)
  let c := (pushforwardRestrictNatIso f U).hom.app
    (tensor X.sheaf ((Scheme.Modules.pullback f).obj L) N)
  have : IsIso a := (tensorSchemeRestrictIso Y U L ((pushforward f).obj N)).isIso_inv
  have : IsIso c := inferInstanceAs (IsIso
    ((pushforwardRestrictNatIso f U).app
      (tensor X.sheaf ((Scheme.Modules.pullback f).obj L) N)).hom)
  have : IsIso (a ≫ b ≫ c) := ‹IsIso (projectionRestrictLeft f U L N)›
  have : IsIso (b ≫ c) := IsIso.of_isIso_comp_left a (b ≫ c)
  exact IsIso.of_isIso_comp_right b c

/-- Projection formula for the tensor sheaf and any line bundle,
proved locally from its pure-section projection morphism. -/
lemma tensorProjection_isIso_of_line (d : LineTrivialization Y.sheaf L) (N : X.Modules) :
    IsIso (tensorProjection f L N) := by
  apply CoherentGlobal.isIso_of_restrict_cover d.obj d.cover
  intro i
  exact projectionRestrict_isIso f L (d.obj i) (d.schemeIso L i) N

/-- The canonical projection-formula isomorphism for any line bundle. -/
def tensorProjectionIso (d : LineTrivialization Y.sheaf L) (N : X.Modules) :
    tensor Y.sheaf L ((pushforward f).obj N) ≅
      (pushforward f).obj (tensor X.sheaf ((Scheme.Modules.pullback f).obj L) N) := by
  have := tensorProjection_isIso_of_line f L d N
  exact asIso (tensorProjection f L N)
end ActualSheafTensor

end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace ActualCartier
open CoherentGlobal ActualSheafTensor Scheme.Modules CoherentK0
variable {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  (f : X ⟶ Y) [IsClosedImmersion f]
  (d : LineTrivialization Y.sheaf (idealSheaf f))

omit [IsLocallyNoetherian X] in
include d in
/-- Tensor by the conormal line preserves coherence on the divisor
by the projection formula and coherent Cartier pullback. -/
lemma coherent_conormal_tensor (N : Coh X) :
    (tensor X.sheaf ((Scheme.Modules.pullback f).obj (idealSheaf f)) N.obj).IsFinitePresentation := by
  let E := (coherentTensorLine (idealSheaf f) d).obj ((cohPushforward f).obj N)
  let T := tensor X.sheaf ((Scheme.Modules.pullback f).obj (idealSheaf f)) N.obj
  have hE : ((Scheme.Modules.pullback f).obj E.obj).IsFinitePresentation :=
    coherent_pullback f d E
  let e : (Scheme.Modules.pullback f).obj E.obj ≅ T :=
    (Scheme.Modules.pullback f).mapIso (tensorProjectionIso f (idealSheaf f) d N.obj) ≪≫
      @asIso _ _ _ _ ((pullbackPushforwardAdjunction f).counit.app T)
        (counitIsIso (pullbackPushforwardAdjunction f) T)
  exact (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso e hE

/-- The conormal twist, as a coherent sheaf ON the Cartier divisor. -/
def conormalTensor (N : Coh X) : Coh X :=
  ⟨tensor X.sheaf ((Scheme.Modules.pullback f).obj (idealSheaf f)) N.obj,
    coherent_conormal_tensor f d N⟩

def conormalProjectionIso (N : Coh X) :
    (coherentTensorLine (idealSheaf f) d).obj ((cohPushforward f).obj N) ≅
      (cohPushforward f).obj (conormalTensor f d N) :=
  ObjectProperty.isoMk _ (tensorProjectionIso f (idealSheaf f) d N.obj)

/-- The first Tor of a supported layer is its tensor by the conormal sheaf on the divisor. -/
def firstTor_supported_iso (N : Coh X) :
    (firstTor f d).obj ((cohPushforward f).obj N) ≅ conormalTensor f d N :=
  (cohPushforward f).preimageIso
    (firstTor_supported_pushforwardIso f d N ≪≫ conormalProjectionIso f d N)

/-- The precise class formula used for each supported layer in the Cartier restriction formula. -/
lemma derivedRestriction_conormal (N : Coh X) :
    derivedRestriction f d (cls ((cohPushforward f).obj N)) =
      cls N - cls (conormalTensor f d N) := by
  rw [derivedRestriction_supported, cls_iso (firstTor_supported_iso f d N)]
end ActualCartier

end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualCartier
open CoherentGlobal ActualSheafTensor CoherentK0
variable {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  (f : X ⟶ Y) [IsClosedImmersion f]
  (d : LineTrivialization Y.sheaf (idealSheaf f))

/-- The coherent Grothendieck identity for an inclusion of torsion-free lattices
whose quotient has a finite filtration by divisor sheaves. -/
lemma lattice_firstTor_identity {S : ShortComplex (Coh Y)} (hS : S.ShortExact)
    (h₁ : ∀ U, Module.IsTorsionFree (Y.sheaf.obj.obj U) (S.X₁.obj.val.obj U))
    (h₂ : ∀ U, Module.IsTorsionFree (Y.sheaf.obj.obj U) (S.X₂.obj.val.obj U))
    (layers : List (Coh X))
    (hlayers : FilteredBy S.X₃ (layers.map (cohPushforward f).obj)) :
    cls ((restriction f d).obj S.X₁) = cls ((restriction f d).obj S.X₂) +
      (layers.map fun Q =>
        cls ((firstTor f d).obj ((cohPushforward f).obj Q)) - cls Q).sum := by
  have h := congrArg (derivedRestriction f d) (cls_shortExact hS)
  rw [map_add, derivedRestriction_cls_torsionFree f d S.X₁ h₁,
    derivedRestriction_cls_torsionFree f d S.X₂ h₂] at h
  have hf := map_cls_filteredBy (derivedRestriction f d) hlayers
  simp only [List.map_map, Function.comp_def, derivedRestriction_supported] at hf
  rw [hf] at h
  have hn : (layers.map fun Q => cls Q -
        cls ((firstTor f d).obj ((cohPushforward f).obj Q))).sum =
      -(layers.map fun Q => cls ((firstTor f d).obj ((cohPushforward f).obj Q)) -
        cls Q).sum := by
    clear hlayers h hf
    induction layers with
    | nil => simp
    | cons Q qs ih =>
      simp only [List.map_cons, List.sum_cons, ih, neg_add_rev]
      abel
  rw [hn] at h
  exact eq_add_of_sub_eq (by simpa only [sub_eq_add_neg] using h.symm)
end ActualCartier

end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualCartier
open CoherentGlobal ActualSheafTensor CoherentK0
variable {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  (f : X ⟶ Y) [IsClosedImmersion f]
  (d : LineTrivialization Y.sheaf (idealSheaf f))

/-- Ordinary restriction is the cokernel of the ideal action. -/
def restrictionCokernelIso (M : Coh Y) :
    (cohPushforward f).obj ((restriction f d).obj M) ≅ cokernel ((action f d).app M) :=
  (restrictionPushforwardIso f d).app M ≪≫
    PreservesCokernel.iso ((evaluation (Coh Y) (Coh Y)).obj M) (action f d)

/-- Repeated images of the Cartier ideal action on a coherent sheaf. -/
abbrev idealMultiple (n : ℕ) (M : Coh Y) : Coh Y :=
  CartierImageFiltration.iterated (coherentTensorLine (idealSheaf f) d) (action f d) n M

/-- The coherent layers of the ideal-adic image filtration. -/
abbrev idealLayers (n : ℕ) (M : Coh Y) : List (Coh X) :=
  CartierImageFiltration.layers (coherentTensorLine (idealSheaf f) d) (action f d)
    (restriction f d).obj n M

omit [IsLocallyNoetherian X] in
lemma filteredBy_idealLayers (n : ℕ) (M : Coh Y) (h : IsZero (idealMultiple f d n M)) :
    FilteredBy M ((idealLayers f d n M).map (cohPushforward f).obj) :=
  CartierImageFiltration.filteredBy_iterated_zero (coherentTensorLine (idealSheaf f) d)
    (action f d) (cohPushforward f) (restriction f d).obj (restrictionCokernelIso f d) n M h

/-- Coherent K₀ identity of the Cartier restriction formula, with each supported
term identified ON the divisor as its conormal tensor. -/
lemma lattice_conormal_identity {S : ShortComplex (Coh Y)} (hS : S.ShortExact)
    (h₁ : ∀ U, Module.IsTorsionFree (Y.sheaf.obj.obj U) (S.X₁.obj.val.obj U))
    (h₂ : ∀ U, Module.IsTorsionFree (Y.sheaf.obj.obj U) (S.X₂.obj.val.obj U))
    (layers : List (Coh X))
    (hlayers : FilteredBy S.X₃ (layers.map (cohPushforward f).obj)) :
    cls ((restriction f d).obj S.X₁) = cls ((restriction f d).obj S.X₂) +
      (layers.map fun Q => cls (conormalTensor f d Q) - cls Q).sum := by
  have h := lattice_firstTor_identity f d hS h₁ h₂ layers hlayers
  simpa only [cls_iso (firstTor_supported_iso f d _)] using h

/-- A nilpotent ideal quotient gives a finite coherent filtration
for the Cartier lattice identity. -/
lemma lattice_nilpotent_identity {S : ShortComplex (Coh Y)} (hS : S.ShortExact)
    (h₁ : ∀ U, Module.IsTorsionFree (Y.sheaf.obj.obj U) (S.X₁.obj.val.obj U))
    (h₂ : ∀ U, Module.IsTorsionFree (Y.sheaf.obj.obj U) (S.X₂.obj.val.obj U))
    (n : ℕ) (hn : IsZero (idealMultiple f d n S.X₃)) :
    cls ((restriction f d).obj S.X₁) = cls ((restriction f d).obj S.X₂) +
      ((idealLayers f d n S.X₃).map fun Q => cls (conormalTensor f d Q) - cls Q).sum :=
  lattice_conormal_identity f d hS h₁ h₂ _ (filteredBy_idealLayers f d n S.X₃ hn)
end ActualCartier

end

noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace CartierImageFiltration
universe u v u' v'
variable {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [HasZeroMorphisms D]
    (T : C ⥤ C) (a : T ⟶ 𝟭 C) (F : C ⥤ D) [F.PreservesZeroMorphisms]

omit [Abelian C] [F.PreservesZeroMorphisms] in
/-- A locally vanishing ideal power remains vanishing at every larger
exponent, by naturality of the iterated action. -/
lemma map_powerAction_zero_of_le (M : C) {n m : ℕ} (hnm : n ≤ m)
    (hn : F.map ((powerAction T a n).app M) = 0) :
    F.map ((powerAction T a m).app M) = 0 := by
  induction m, hnm using Nat.le_induction with
  | base => exact hn
  | succ m hm ih =>
    have he := (powerAction T a m).naturality (a.app M)
    simp only [Functor.id_map, Functor.id_obj] at he
    change F.map ((powerAction T a m).app (T.obj M) ≫ a.app M) = 0
    rw [← he, F.map_comp, ih, comp_zero]
end CartierImageFiltration

namespace ActualCartier
open CoherentGlobal ActualSheafTensor CartierImageFiltration
variable {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsClosedImmersion f]
    (d : LineTrivialization Y.sheaf (idealSheaf f))

omit [IsLocallyNoetherian X] [IsClosedImmersion f] in
/-- Finitely many locally vanishing Cartier powers give a global nilpotence
exponent and a finite supported filtration. -/
lemma idealMultiple_isZero_of_finite_cover
    {ι : Type} [Fintype ι] (U : ι → Y.Opens)
    (hU : (Opens.grothendieckTopology Y).CoversTop U) (M : Coh Y)
    (h : ∀ i, ∃ n : ℕ,
      (((cohInclusion Y).map
        ((powerAction (coherentTensorLine (idealSheaf f) d) (action f d) n).app M)).over
          (U i)) = 0) :
    ∃ n : ℕ, IsZero (idealMultiple f d n M) := by
  classical
  choose k hk using h
  let N : ℕ := ∑ i, k i
  refine ⟨N, iterated_isZero_of_powerAction_zero _ _ N M ?_⟩
  apply (cohInclusion Y).map_injective
  erw [Functor.map_zero]
  apply SheafLocality.module_hom_ext_of_coversTop Y.ringCatSheaf hU
  intro i
  have : (SheafOfModules.overFunctor Y.ringCatSheaf (U i)).PreservesZeroMorphisms :=
    ⟨fun _ _ => rfl⟩
  erw [Functor.map_zero]
  let F := cohInclusion Y ⋙ SheafOfModules.overFunctor Y.ringCatSheaf (U i)
  have hn : k i ≤ N := Finset.single_le_sum (fun j _ => Nat.zero_le (k j))
    (Finset.mem_univ i)
  exact map_powerAction_zero_of_le _ _ F M hn (hk i)
end ActualCartier

end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
open scoped BigOperators
namespace CartierAffineCoverNilpotence
open Scheme.Modules ActualSheafTensor CartierImageFiltration
variable {Y : Scheme.{0}} {ι : Type} [Fintype ι]
    (R : ι → CommRingCat.{0}) (f : ∀ i, Spec (R i) ⟶ Y)
    [∀ i, IsOpenImmersion (f i)]
    (hcover : (⨆ i, (f i).opensRange) = ⊤)
    (L : Y.Modules) (i : L ⟶ SheafOfModules.unit Y.ringCatSheaf)
    (e : ∀ j, (restrictFunctor (f j)).obj L ≅ SheafOfModules.unit (Spec (R j)).ringCatSheaf)

include hcover

/-- Support on finitely many principal Cartier charts gives a vanishing tensor-ideal power. -/
lemma exists_powerAction_zero (M : Y.Modules) [M.IsFinitePresentation]
    (hM : ∀ j, IsZero (((restrictFunctor (f j)).obj M).over
      (PrimeSpectrum.basicOpen (AffineCartierNilpotence.equation
        ((restrictFunctor (f j)).obj L) (e j) (restrictedIdeal (f j) i))))) :
    ∃ n : ℕ, (powerAction (tensorLeft Y.sheaf L) (idealAction Y.sheaf i) n).app M = 0 := by
  classical
  have hlocal (j : ι) : ∃ n : ℕ, (restrictFunctor (f j)).map
      ((powerAction (tensorLeft Y.sheaf L) (idealAction Y.sheaf i) n).app M) = 0 := by
    have : ((restrictFunctor (f j)).obj M).IsFinitePresentation :=
      CoherentGlobal.coherent_restrict (f j) M
    obtain ⟨n, hn⟩ := AffineCartierNilpotence.coherent_powerAction_zero_of_puncture_zero
      ((restrictFunctor (f j)).obj L) (e j) (restrictedIdeal (f j) i)
      ((restrictFunctor (f j)).obj M) (hM j)
    refine ⟨n, map_powerAction_zero_of_comparison
      (tensorLeft Y.sheaf L) (tensorLeft (Spec (R j)).sheaf ((restrictFunctor (f j)).obj L))
      (restrictFunctor (f j)) (tensorOpenRestrictNatIso (f j) L)
      (idealAction Y.sheaf i) (idealAction (Spec (R j)).sheaf (restrictedIdeal (f j) i))
      (tensorOpenRestrict_action (f j) i) n M hn⟩
  choose k hk using hlocal
  let n : ℕ := ∑ j, k j
  refine ⟨n, SheafLocality.module_zero_of_openCover (fun j => Spec (R j)) f hcover _ ?_⟩
  intro j
  apply map_powerAction_zero_of_le _ _ (restrictFunctor (f j)) M
    (show k j ≤ n from Finset.single_le_sum (fun l _ => Nat.zero_le (k l)) (Finset.mem_univ j))
  exact hk j
end CartierAffineCoverNilpotence

end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace ActualCartier
open CoherentGlobal ActualSheafTensor CoherentK0
variable {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  (f : X ⟶ Y) [IsClosedImmersion f]
  (d : LineTrivialization Y.sheaf (idealSheaf f))

instance firstTor_additive : (firstTor f d).Additive := by
  have : (kernel (action f d)).Additive :=
    kernel_functor_additive _ _ (action f d)
  have : (firstTor f d ⋙ cohPushforward f).Additive :=
    Functor.additive_of_iso (firstTorPushforwardIso f d).symm
  exact Functor.additive_of_comp_faithful (firstTor f d) (cohPushforward f)

instance restriction_additive : (restriction f d).Additive := by
  have : (cokernel (action f d)).Additive :=
    cokernel_functor_additive _ _ (action f d)
  have : (restriction f d ⋙ cohPushforward f).Additive :=
    Functor.additive_of_iso (restrictionPushforwardIso f d).symm
  exact Functor.additive_of_comp_faithful (restriction f d) (cohPushforward f)
end ActualCartier

end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualCartier
open CoherentGlobal ActualSheafTensor CoherentK0 CartierImageFiltration
variable {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  (f : X ⟶ Y) [IsClosedImmersion f]
  (d : LineTrivialization Y.sheaf (idealSheaf f))

instance restrictionUnit_epi (M : Coh Y) : Epi ((restrictionUnit f d).app M) := by
  dsimp only [restrictionUnit, NatTrans.comp_app]
  infer_instance

instance restriction_preservesEpis : (restriction f d).PreservesEpimorphisms where
  preserves {M N} e he := by
    have h : (restrictionUnit f d).app M ≫
        (cohPushforward f).map ((restriction f d).map e) =
        e ≫ (restrictionUnit f d).app N :=
      ((restrictionUnit f d).naturality e).symm
    have : Epi (e ≫ (restrictionUnit f d).app N) := inferInstance
    have : Epi ((cohPushforward f).map ((restriction f d).map e)) := epi_of_epi_fac h
    exact (cohPushforward f).epi_of_epi_map inferInstance

/-- The jth supported quotient of the ideal-image filtration. -/
abbrev layer (j : ℕ) (M : Coh Y) : Coh X :=
  (restriction f d).obj (idealMultiple f d j M)

/-- An ambient ideal power of the original lattice surjects onto each
corresponding layer of its quotient. -/
def layerCover {L Q : Coh Y} (q : L ⟶ Q) (j : ℕ) :
    (CartierImageFiltration.power (coherentTensorLine (idealSheaf f) d) j).obj L ⟶
      (cohPushforward f).obj (layer f d j Q) :=
  (CartierImageFiltration.power (coherentTensorLine (idealSheaf f) d) j).map q ≫
    powerToImage (coherentTensorLine (idealSheaf f) d) (action f d) j Q ≫
      (restrictionUnit f d).app (idealMultiple f d j Q)

instance layerCover_epi {L Q : Coh Y} (q : L ⟶ Q) [Epi q] (j : ℕ) :
    Epi (layerCover f d q j) := by
  dsimp only [layerCover]
  infer_instance

/-- The quotient morphism on the Cartier divisor. -/
def layerQuotient {L Q : Coh Y} (q : L ⟶ Q) (j : ℕ) :
    (restriction f d).obj
      ((CartierImageFiltration.power (coherentTensorLine (idealSheaf f) d) j).obj L) ⟶
      layer f d j Q :=
  (restriction f d).map (layerCover f d q j) ≫
    (restriction_supported_iso f d (layer f d j Q)).hom

instance layerQuotient_epi {L Q : Coh Y} (q : L ⟶ Q) [Epi q] (j : ℕ) :
    Epi (layerQuotient f d q j) := by
  dsimp only [layerQuotient]
  infer_instance

/-- An ideal-power containment in a lattice inclusion gives nilpotence
and coherent layers in the conormal Grothendieck identity. -/
lemma lattice_sandwich_identity {S : ShortComplex (Coh Y)} (hS : S.ShortExact)
    (h₁ : ∀ U, Module.IsTorsionFree (Y.sheaf.obj.obj U) (S.X₁.obj.val.obj U))
    (h₂ : ∀ U, Module.IsTorsionFree (Y.sheaf.obj.obj U) (S.X₂.obj.val.obj U))
    (n : ℕ)
    (b : (CartierImageFiltration.power (coherentTensorLine (idealSheaf f) d) n).obj S.X₂ ⟶ S.X₁)
    (hb : b ≫ S.f =
      (CartierImageFiltration.powerAction (coherentTensorLine (idealSheaf f) d) (action f d) n).app S.X₂) :
    cls ((restriction f d).obj S.X₁) = cls ((restriction f d).obj S.X₂) +
      ((idealLayers f d n S.X₃).map fun Q => cls (conormalTensor f d Q) - cls Q).sum := by
  apply lattice_nilpotent_identity f d hS h₁ h₂ n
  apply iterated_isZero_of_powerAction_zero
  exact powerAction_quotient_zero _ _ hS n b hb
end ActualCartier

end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace ActualCartier
open CoherentGlobal ActualSheafTensor CartierImageFiltration
variable {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsClosedImmersion f]
    (d : LineTrivialization Y.sheaf (idealSheaf f))

/-- Tensor by the conormal line, on coherent sheaves of the divisor. -/
def conormalFunctor : Coh X ⥤ Coh X :=
  (SheafOfModules.isFinitePresentation X.ringCatSheaf).lift
    (cohInclusion X ⋙ tensorLeft X.sheaf ((Scheme.Modules.pullback f).obj (idealSheaf f)))
    (coherent_conormal_tensor f d)

omit [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsClosedImmersion f] in
lemma action_central (M : Coh Y) :
    (action f d).app ((coherentTensorLine (idealSheaf f) d).obj M) =
      (coherentTensorLine (idealSheaf f) d).map ((action f d).app M) := by
  apply ObjectProperty.hom_ext
  exact idealAction_central Y.sheaf d (idealι f) M.obj

/-- Cartier restriction sends an ideal twist to the conormal twist
by preservation of cokernels and centrality of multiplication. -/
def restriction_tensorLine_iso (M : Coh Y) :
    (restriction f d).obj ((coherentTensorLine (idealSheaf f) d).obj M) ≅
      (conormalFunctor f d).obj ((restriction f d).obj M) := by
  let T := coherentTensorLine (idealSheaf f) d
  have : PreservesFiniteColimits T := T.preservesFiniteColimits_of_preservesHomology
  apply (cohPushforward f).preimageIso
  exact restrictionCokernelIso f d (T.obj M) ≪≫
    cokernelIsoOfEq (action_central f d M) ≪≫
    (PreservesCokernel.iso T ((action f d).app M)).symm ≪≫
    T.mapIso (restrictionCokernelIso f d M).symm ≪≫
    conormalProjectionIso f d ((restriction f d).obj M)

/-- Restricting each ambient ideal power gives the corresponding
conormal tensor power on the divisor. -/
def restriction_powerIso : (j : ℕ) → (M : Coh Y) →
    (restriction f d).obj ((power (coherentTensorLine (idealSheaf f) d) j).obj M) ≅
      (power (conormalFunctor f d) j).obj ((restriction f d).obj M)
  | 0, _ => Iso.refl _
  | j + 1, M => restriction_powerIso j ((coherentTensorLine (idealSheaf f) d).obj M) ≪≫
      (power (conormalFunctor f d) j).mapIso (restriction_tensorLine_iso f d M)

/-- The surjection from the jth conormal twist of the original
restricted lattice onto its jth supported quotient (the ideal-image filtration). -/
def twistedLayerQuotient {L Q : Coh Y} (q : L ⟶ Q) (j : ℕ) :
    (power (conormalFunctor f d) j).obj ((restriction f d).obj L) ⟶ layer f d j Q :=
  (restriction_powerIso f d j L).inv ≫ layerQuotient f d q j

instance twistedLayerQuotient_epi {L Q : Coh Y} (q : L ⟶ Q) [Epi q] (j : ℕ) :
    Epi (twistedLayerQuotient f d q j) := by
  dsimp only [twistedLayerQuotient]
  infer_instance
end ActualCartier

end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace ActualCartier
open CoherentGlobal ActualSheafTensor CartierImageFiltration CoherentK0 Scheme.Modules
variable {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (g : X ⟶ Y) [IsClosedImmersion g]
    (d : LineTrivialization Y.sheaf (idealSheaf g))
    {ι : Type} [Fintype ι] (R : ι → CommRingCat.{0})
    (f : ∀ j, Spec (R j) ⟶ Y) [∀ j, IsOpenImmersion (f j)]
    (hcover : (⨆ j, (f j).opensRange) = ⊤)
    (e : ∀ j, (restrictFunctor (f j)).obj (idealSheaf g) ≅
      SheafOfModules.unit (Spec (R j)).ringCatSheaf)

include hcover

omit [IsLocallyNoetherian X] [IsClosedImmersion g] in
/-- Support on the finite principal-chart complement yields a finite
filtration by the Cartier ideal images in the coherent category. -/
lemma exists_idealMultiple_isZero_of_support (M : Coh Y)
    (hM : ∀ j, IsZero (((restrictFunctor (f j)).obj M.obj).over
      (PrimeSpectrum.basicOpen (AffineCartierNilpotence.equation
        ((restrictFunctor (f j)).obj (idealSheaf g)) (e j)
        (restrictedIdeal (f j) (idealι g)))))) :
    ∃ n : ℕ, IsZero (idealMultiple g d n M) := by
  have := M.property
  obtain ⟨n, hn⟩ := CartierAffineCoverNilpotence.exists_powerAction_zero
    R f hcover (idealSheaf g) (idealι g) e M.obj hM
  refine ⟨n, iterated_isZero_of_powerAction_zero _ _ n M ?_⟩
  apply (cohInclusion Y).map_injective
  erw [Functor.map_zero]
  let T := coherentTensorLine (idealSheaf g) d
  let S := tensorLeft Y.sheaf (idealSheaf g)
  let F := cohInclusion Y
  let c : T ⋙ F ≅ F ⋙ S := Iso.refl _
  exact map_powerAction_zero_of_comparison T S F c (action g d)
    (idealAction Y.sheaf (idealι g)) (fun _ => Category.id_comp _) n M hn

/-- The divisor-side Grothendieck lattice identity follows from local support. -/
lemma lattice_support_identity {S : ShortComplex (Coh Y)} (hS : S.ShortExact)
    (h₁ : ∀ U, Module.IsTorsionFree (Y.sheaf.obj.obj U) (S.X₁.obj.val.obj U))
    (h₂ : ∀ U, Module.IsTorsionFree (Y.sheaf.obj.obj U) (S.X₂.obj.val.obj U))
    (hQ : ∀ j, IsZero (((restrictFunctor (f j)).obj S.X₃.obj).over
      (PrimeSpectrum.basicOpen (AffineCartierNilpotence.equation
        ((restrictFunctor (f j)).obj (idealSheaf g)) (e j)
        (restrictedIdeal (f j) (idealι g)))))) :
    ∃ n : ℕ, cls ((restriction g d).obj S.X₁) = cls ((restriction g d).obj S.X₂) +
      ((idealLayers g d n S.X₃).map fun Q => cls (conormalTensor g d Q) - cls Q).sum := by
  obtain ⟨n, hn⟩ := exists_idealMultiple_isZero_of_support g d R f hcover e S.X₃ hQ
  exact ⟨n, lattice_nilpotent_identity g d hS h₁ h₂ n hn⟩
end ActualCartier

end

end OAI
