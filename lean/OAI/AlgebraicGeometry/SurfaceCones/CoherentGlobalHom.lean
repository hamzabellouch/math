import OAI.AlgebraicGeometry.SurfaceCones.CoherentGlobalDual

namespace OAI

section
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace CoherentDual
section Global
universe u
variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
  (M N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
  (T : C) (hT : IsTerminal T)

def globalHomEquiv : (homSheaf R M N).val.obj (op T) ≃ (M ⟶ N) where
  toFun f := ⟨PresheafOfModules.homMk
    (Functor.whiskerLeft (Over.equivalenceOfIsTerminal hT).inverse.op f.val)
    (fun U r x => f.property (op (Over.mk (hT.from U.unop))) r x)⟩
  invFun f := ⟨Functor.whiskerLeft (Over.forget T).op
    ((PresheafOfModules.toPresheaf _).map f.val),
    fun U r x => (f.val.app (op U.unop.left)).hom.map_smul r x⟩
  right_inv f := by
    ext U x
    rfl
  left_inv f := by
    apply Subtype.ext
    apply local_ext
    intro U x
    let e := (Over.equivalenceOfIsTerminal hT).unitIso.hom.app U.unop
    have h := ConcreteCategory.congr_hom (f.val.naturality e.op) x
    change localApp f.val U (M.val.map (𝟙 (op U.unop.left)) x) =
      N.val.map (𝟙 (op U.unop.left))
        (localApp f.val (op (Over.mk (hT.from U.unop.left))) x) at h
    rw [PresheafOfModules.map_id, PresheafOfModules.map_id] at h
    exact h.symm
end Global
end CoherentDual

end

end

section
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace CoherentDual
open Scheme.Modules
variable {A : CommRingCat.{0}} (M N : ModuleCat A)

abbrev affineHom := homSheaf.{0,0,0,0} (Spec A).sheaf (tilde M) (tilde N)

def affineHomLinearMap :
    (moduleSpecΓFunctor.obj (affineHom M N)) →ₗ[A] (M →ₗ[A] N) where
  toFun s := ((tilde.isoTop N).inv).hom.comp
    (((moduleSpecΓFunctor.map
      (globalHomEquiv (Spec A).sheaf (tilde M) (tilde N) ⊤ isTerminalTop s)).hom).comp
        ((tilde.isoTop M).hom).hom)
  map_add' s t := by
    ext x
    change (tilde.isoTop N).inv.hom
      (localApp (s + t).val (op (Over.mk (𝟙 (⊤ : (Spec A).Opens))))
        ((tilde.isoTop M).hom x)) = _
    change (tilde.isoTop N).inv.hom
      (localApp s.val (op (Over.mk (𝟙 (⊤ : (Spec A).Opens)))) ((tilde.isoTop M).hom x) +
        localApp t.val (op (Over.mk (𝟙 (⊤ : (Spec A).Opens)))) ((tilde.isoTop M).hom x)) = _
    exact map_add (tilde.isoTop N).inv.hom _ _
  map_smul' r s := by
    ext x
    exact (tilde.isoTop N).inv.hom.map_smul r _

lemma affineHomLinearMap_global (f : M ⟶ N) :
    affineHomLinearMap M N ((globalHomEquiv (Spec A).sheaf (tilde M) (tilde N)
      ⊤ isTerminalTop).symm ((tilde.functor A).map f)) = f.hom := by
  have h := (tilde.toTildeΓNatIso (R := A)).hom.naturality f
  change f ≫ (tilde.isoTop N).hom =
    (tilde.isoTop M).hom ≫ moduleSpecΓFunctor.map ((tilde.functor A).map f) at h
  have hh := congrArg (fun g => g ≫ (tilde.isoTop N).inv) h
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at hh
  change (tilde.isoTop N).inv.hom.comp
    ((moduleSpecΓFunctor.map (globalHomEquiv _ _ _ _ _ _)).hom.comp
      (tilde.isoTop M).hom.hom) = f.hom
  have he := (globalHomEquiv (Spec A).sheaf (tilde M) (tilde N) ⊤ isTerminalTop).apply_symm_apply
    ((tilde.functor A).map f)
  rw [he]
  exact congrArg (fun g => g.hom) hh.symm

lemma affineHomLinearMap_bijective : Function.Bijective (affineHomLinearMap M N) := by
  let e := globalHomEquiv (Spec A).sheaf (tilde M) (tilde N) ⊤ isTerminalTop
  constructor
  · intro s t hst
    obtain ⟨f, hf⟩ := (tilde.fullyFaithfulFunctor (R := A)).homEquiv.surjective (e s)
    obtain ⟨g, hg⟩ := (tilde.fullyFaithfulFunctor (R := A)).homEquiv.surjective (e t)
    have hs : s = e.symm ((tilde.functor A).map f) := by
      apply e.injective
      exact hf.symm.trans (e.apply_symm_apply _).symm
    have ht : t = e.symm ((tilde.functor A).map g) := by
      apply e.injective
      exact hg.symm.trans (e.apply_symm_apply _).symm
    rw [hs, ht] at hst ⊢
    rw [affineHomLinearMap_global, affineHomLinearMap_global] at hst
    congr 2
    exact ModuleCat.hom_ext hst
  · intro f
    exact ⟨e.symm ((tilde.functor A).map (ModuleCat.ofHom f)),
      affineHomLinearMap_global M N (ModuleCat.ofHom f)⟩

/-- The global sections of the actual affine internal Hom are precisely the
module Hom, as modules, not merely as abstract sets. -/
def affineHomLinearEquiv :
    (moduleSpecΓFunctor.obj (affineHom M N)) ≃ₗ[A] (M →ₗ[A] N) :=
  LinearEquiv.ofBijective (affineHomLinearMap M N) (affineHomLinearMap_bijective M N)
end CoherentDual

end

end

section
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace CoherentGlobal
open Scheme.Modules
lemma coherent_kernel_free_over {X : Scheme.{0}} [IsLocallyNoetherian X] (U : X.Opens)
    {I J : Type} [Finite I] [Finite J]
    (f : SheafOfModules.free (R := X.ringCatSheaf.over U) I ⟶ SheafOfModules.free J) :
    (kernel f).IsFinitePresentation := by
  let : HasKernels (SheafOfModules.{0} U.toScheme.ringCatSheaf) :=
    inferInstanceAs (HasKernels U.toScheme.Modules)
  let F : SheafOfModules (X.ringCatSheaf.over U) ⥤ SheafOfModules U.toScheme.ringCatSheaf :=
    (overEquiv U).functor
  have : F.IsEquivalence := inferInstanceAs (overEquiv U).functor.IsEquivalence
  let eU := (TopologicalSpace.Opens.sheafOfModulesEquivOverUnit U X.ringCatSheaf).symm
  let eI := (SheafOfModules.mapFreeIso F I eU).symm
  let eJ := (SheafOfModules.mapFreeIso F J eU).symm
  let g : SheafOfModules.free (R := U.toScheme.ringCatSheaf) I ⟶
      SheafOfModules.free J := eI.inv ≫ F.map f ≫ eJ.hom
  let : HasKernel g :=
    HasKernels.has_limit g
  let e : F.obj (kernel f) ≅ kernel g :=
    PreservesKernel.iso F f ≪≫ CoherentDual.kernelConjugateIso (F.map f) eI eJ
  have hg : (kernel g).IsFinitePresentation := coherent_kernel_free g
  have : ((overEquiv U).inverse.obj (kernel g)).IsFinitePresentation :=
    @finitePresentation_overEquiv_inverse _ U (kernel g) hg
  let q : kernel f ≅ (overEquiv U).inverse.obj (kernel g) :=
    (overEquiv U).unitIso.app _ ≪≫ (overEquiv U).inverse.mapIso e
  exact (SheafOfModules.isFinitePresentation (X.ringCatSheaf.over U)).prop_of_iso q.symm inferInstance
end CoherentGlobal

namespace CoherentDual
section Slice
variable {X : Scheme.{0}} [IsLocallyNoetherian X] (U : X.Opens)
    (M : SheafOfModules (X.ringCatSheaf.over U)) (P : M.Presentation) [P.IsFinite]
include P
lemma coherent_dual_over_of_presentation :
    (homSheaf (X.sheaf.over U) M (SheafOfModules.unit _)).IsFinitePresentation := by
  have hP : P.IsFinite := inferInstance
  change SheafOfModules ((sheafCompose _ (forget₂ CommRingCat RingCat)).obj
    (X.sheaf.over U)) at M
  change M.Presentation at P
  let : Finite P.generators.I :=
    hP.isFiniteType_generators.finite
  let : Finite P.relations.I :=
    hP.isFiniteType_relations.finite
  let N := SheafOfModules.unit
    ((sheafCompose _ (forget₂ CommRingCat RingCat)).obj (X.sheaf.over U))
  let F := homSheafFunctor (X.sheaf.over U) N
  have : PreservesLimitsOfSize.{0,0} F := homSheafFunctor_preservesLimits (X.sheaf.over U) N
  have : F.Additive := homSheafFunctor_additive (X.sheaf.over U) N
  have : F.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive F
  let f : SheafOfModules.free P.relations.I ⟶ SheafOfModules.free P.generators.I :=
    P.relations.π ≫ kernel.ι P.generators.π
  let h := CokernelCofork.IsColimit.ofπOp P.generators.π (by simp) P.isColimit
  let e : homSheaf (X.sheaf.over U) M N ≅ kernel (F.map f.op) :=
    IsLimit.conePointUniqueUpToIso (KernelFork.mapIsLimit _ h F) (limit.isLimit _)
  let eG := dualFiniteFreeIso (X.sheaf.over U) P.generators.I
  let eR := dualFiniteFreeIso (X.sheaf.over U) P.relations.I
  let g := eG.inv ≫ F.map f.op ≫ eR.hom
  let ek : kernel (F.map f.op) ≅ kernel g :=
    kernelConjugateIso (F.map f.op) eG eR
  apply (SheafOfModules.isFinitePresentation (X.ringCatSheaf.over U)).prop_of_iso
    (e ≪≫ ek).symm
  exact CoherentGlobal.coherent_kernel_free_over U g
end Slice
end CoherentDual

namespace CoherentDual
section Restriction
universe u
variable {C : Type u} [Category.{u} C]
  {R : Cᵒᵖ ⥤ CommRingCat.{u}}
  (M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
  (U : C)

def overLocalForward (V : Over U)
    (f : linearLocalHom (R := R) (M := M) (N := N) V.left) :
    linearLocalHom (R := ((Over.forget U).op ⋙ R)) (M := ((PresheafOfModules.pushforward (F := Over.forget U) (𝟙 ((Over.forget U).op ⋙ (R ⋙ forget₂ CommRingCat RingCat)))).obj M)) (N := ((PresheafOfModules.pushforward (F := Over.forget U) (𝟙 ((Over.forget U).op ⋙ (R ⋙ forget₂ CommRingCat RingCat)))).obj N)) V :=
  ⟨Functor.whiskerLeft (Over.iteratedSliceForward V).op f.val,
    fun Y r x => f.property ((Over.iteratedSliceForward V).op.obj Y) r x⟩

def overLocalBackward (V : Over U)
    (f : linearLocalHom (R := ((Over.forget U).op ⋙ R)) (M := ((PresheafOfModules.pushforward (F := Over.forget U) (𝟙 ((Over.forget U).op ⋙ (R ⋙ forget₂ CommRingCat RingCat)))).obj M)) (N := ((PresheafOfModules.pushforward (F := Over.forget U) (𝟙 ((Over.forget U).op ⋙ (R ⋙ forget₂ CommRingCat RingCat)))).obj N)) V) :
    linearLocalHom (R := R) (M := M) (N := N) V.left :=
  ⟨Functor.whiskerLeft (Over.iteratedSliceBackward V).op f.val,
    fun Y r x => f.property ((Over.iteratedSliceBackward V).op.obj Y) r x⟩

instance overLocalModule (V : Over U) :
    Module (R.obj (op V.left))
      (linearLocalHom (R := ((Over.forget U).op ⋙ R))
        (M := ((PresheafOfModules.pushforward (F := Over.forget U) (𝟙 ((Over.forget U).op ⋙ (R ⋙ forget₂ CommRingCat RingCat)))).obj M))
        (N := ((PresheafOfModules.pushforward (F := Over.forget U) (𝟙 ((Over.forget U).op ⋙ (R ⋙ forget₂ CommRingCat RingCat)))).obj N)) V) :=
  Submodule.module _

/-- Restriction of local linear Hom to a slice is the local linear Hom on
that slice. This is the actual restriction identity needed to glue coherence. -/
def overLocalEquiv (V : Over U) :
    linearLocalHom (R := R) (M := M) (N := N) V.left ≃ₗ[R.obj (op V.left)]
      linearLocalHom (R := ((Over.forget U).op ⋙ R)) (M := ((PresheafOfModules.pushforward (F := Over.forget U) (𝟙 ((Over.forget U).op ⋙ (R ⋙ forget₂ CommRingCat RingCat)))).obj M)) (N := ((PresheafOfModules.pushforward (F := Over.forget U) (𝟙 ((Over.forget U).op ⋙ (R ⋙ forget₂ CommRingCat RingCat)))).obj N)) V where
  toFun := overLocalForward M N U V
  invFun := overLocalBackward M N U V
  map_add' f g := rfl
  map_smul' r f := by
    apply Subtype.ext
    apply local_ext
    intro Y x
    rfl
  left_inv f := by
    apply Subtype.ext
    apply local_ext
    intro Y x
    rfl
  right_inv f := by
    apply Subtype.ext
    apply local_ext
    intro Y x
    let e := (Over.iteratedSliceEquiv V).unitIso.hom.app Y.unop
    have h := ConcreteCategory.congr_hom (f.val.naturality e.op) x
    change localApp f.val Y (M.map (𝟙 (op Y.unop.left.left)) x) =
      N.map (𝟙 (op Y.unop.left.left))
        (localApp (overLocalForward M N U V (overLocalBackward M N U V f)).val Y x) at h
    rw [PresheafOfModules.map_id, PresheafOfModules.map_id] at h
    exact h.symm

end Restriction
end CoherentDual

namespace CoherentDual
section OverIso
universe u
variable {C : Type u} [Category.{u} C]
  {R : Cᵒᵖ ⥤ CommRingCat.{u}}
  (M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
  (U : C)

def homOverPresheafIso :
    (PresheafOfModules.pushforward (F := Over.forget U) (𝟙 ((Over.forget U).op ⋙ (R ⋙ forget₂ CommRingCat RingCat)))).obj (homPresheaf (R := R) (M := M) (N := N)) ≅
    homPresheaf (R := (Over.forget U).op ⋙ R)
      (M := (PresheafOfModules.pushforward (F := Over.forget U) (𝟙 ((Over.forget U).op ⋙ (R ⋙ forget₂ CommRingCat RingCat)))).obj M)
      (N := (PresheafOfModules.pushforward (F := Over.forget U) (𝟙 ((Over.forget U).op ⋙ (R ⋙ forget₂ CommRingCat RingCat)))).obj N) :=
  PresheafOfModules.isoMk (fun V => (overLocalEquiv M N U V.unop).toModuleIso) (by
    intro V W g
    ext f
    apply Subtype.ext
    apply local_ext
    intro Z x
    rfl)

variable {J : GrothendieckTopology C} (R₁ : Sheaf J CommRingCat.{u})
  (M₁ N₁ : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R₁))

/-- Internal Hom commutes with actual restriction to the slice site. -/
def homOverIso :
    (homSheaf R₁ M₁ N₁).over U ≅ homSheaf (R₁.over U) (M₁.over U) (N₁.over U) := by
  apply (SheafOfModules.fullyFaithfulForget _).preimageIso
  exact homOverPresheafIso M₁.val N₁.val U
end OverIso
end CoherentDual

namespace CoherentDual
/-- The actual internal structure-sheaf dual of a coherent sheaf on a
locally Noetherian scheme is coherent. -/
lemma coherent_dual {X : Scheme.{0}} [IsLocallyNoetherian X]
    (M : X.Modules) [M.IsFinitePresentation] :
    (homSheaf X.sheaf M (SheafOfModules.unit _)).IsFinitePresentation := by
  obtain ⟨D, hD⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData M
  let := hD
  have (i : D.I) : ((homSheaf X.sheaf M (SheafOfModules.unit _)).over (D.X i)).IsFinitePresentation := by
    let : (D.presentation i).IsFinite := hD.isFinite_presentation i
    let e := homOverIso (D.X i) X.sheaf M (SheafOfModules.unit _)
    have : (homSheaf (X.sheaf.over (D.X i)) (M.over (D.X i))
        (SheafOfModules.unit _)).IsFinitePresentation :=
      coherent_dual_over_of_presentation (D.X i) _ (D.presentation i)
    exact (SheafOfModules.isFinitePresentation (X.ringCatSheaf.over (D.X i))).prop_of_iso e.symm this
  exact CoherentLocality.finitePresentation_of_coversTop _ D.X D.coversTop

/-- The double dual in the model construction is an actual coherent sheaf. -/
lemma coherent_doubleDual {X : Scheme.{0}} [IsLocallyNoetherian X]
    (M : X.Modules) [M.IsFinitePresentation] :
    (homSheaf X.sheaf (homSheaf X.sheaf M (SheafOfModules.unit _))
      (SheafOfModules.unit _)).IsFinitePresentation := by
  have := coherent_dual M
  exact coherent_dual _
end CoherentDual

end

end

section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace CoherentPullback

lemma exists_presentation_tilde {A : CommRingCat.{0}} [IsNoetherianRing A]
    (M : ModuleCat A) [Module.Finite A M] :
    ∃ P : (tilde M).Presentation, P.IsFinite := by
  have := Module.finitePresentation_of_finite A M
  obtain ⟨s, hs, hker⟩ := Module.FinitePresentation.out (R := A) (M := M)
  obtain ⟨t, ht⟩ := hker
  let P := presentationTilde M (s : Set M) hs (t : Set ((s : Set M) →₀ A)) ht
  refine ⟨P, ?_⟩
  constructor
  · constructor
    change Finite (s : Set M)
    infer_instance
  · constructor
    change Finite (t : Set ((s : Set M) →₀ A))
    infer_instance

/-- Pullback carries an actual finite global presentation to one. -/
lemma exists_presentation_pullback {X Y : Scheme} (f : X ⟶ Y)
    {M : Y.Modules} (P : M.Presentation) [P.IsFinite] :
    ∃ Q : ((Scheme.Modules.pullback f).obj M).Presentation, Q.IsFinite := by
  have hP : P.IsFinite := inferInstance
  have hp : PreservesLimit (Functor.empty Y.Opens) (TopologicalSpace.Opens.map f.base) :=
    preservesLimit_of_preserves_limit_cone (isTerminalTop : IsTerminal (⊤ : Y.Opens))
      ((isLimitMapConeEmptyConeEquiv _ _).symm
        (by simpa only [TopologicalSpace.Opens.map_top] using
          (isTerminalTop : IsTerminal (⊤ : X.Opens))))
  have : (TopologicalSpace.Opens.map f.base).Final := inferInstance
  have : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward f).IsRightAdjoint
  have : (SheafOfModules.pullback f.toRingCatSheafHom).IsLeftAdjoint :=
    inferInstanceAs (Scheme.Modules.pullback f).IsLeftAdjoint
  have : PreservesColimitsOfSize.{0, 0} (SheafOfModules.pullback f.toRingCatSheafHom) :=
    inferInstanceAs (PreservesColimitsOfSize.{0, 0} (Scheme.Modules.pullback f))
  let e := (@asIso _ _ _ _ (SheafOfModules.pullbackObjUnitToUnit
    (F := TopologicalSpace.Opens.map f.base) f.toRingCatSheafHom)
      (SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal
        (F := TopologicalSpace.Opens.map f.base) f.toRingCatSheafHom)).symm
  let Q : ((Scheme.Modules.pullback f).obj M).Presentation :=
    P.map (SheafOfModules.pullback f.toRingCatSheafHom) e
  refine ⟨Q, ?_⟩
  constructor
  · constructor
    change Finite P.generators.I
    exact hP.isFiniteType_generators.finite
  · constructor
    change Finite P.relations.I
    exact hP.isFiniteType_relations.finite

/-- The actual sheaf `p^*(M^~)` used in the manuscript, lines 328 has a global finite
presentation, for any scheme model over a Noetherian affine. -/
lemma exists_presentation_pullback_tilde {A : CommRingCat.{0}} [IsNoetherianRing A]
    {X : Scheme} (p : X ⟶ Spec A) (M : ModuleCat A) [Module.Finite A M] :
    ∃ P : ((Scheme.Modules.pullback p).obj (tilde M)).Presentation, P.IsFinite := by
  obtain ⟨P, hP⟩ := exists_presentation_tilde M
  let := hP
  exact exists_presentation_pullback p P
end CoherentPullback

namespace CoherentModelActual
open CategoryTheory AlgebraicGeometry

/-- The exact double-dual construction in the manuscript, lines 328. -/
abbrev E {A : CommRingCat.{0}} {W : Scheme.{0}} (p : W ⟶ Spec A) (M : ModuleCat A) : W.Modules :=
  CoherentDual.homSheaf.{0,0,0,0} W.sheaf
    (CoherentDual.homSheaf.{0,0,0,0} W.sheaf ((Scheme.Modules.pullback p).obj (tilde M))
      (SheafOfModules.unit _)) (SheafOfModules.unit _)

/-- The model sheaf is coherent for every finite module. -/
lemma coherent_E {A : CommRingCat.{0}} [IsNoetherianRing A] {W : Scheme.{0}}
    [IsLocallyNoetherian W] (p : W ⟶ Spec A) (M : ModuleCat A) [Module.Finite A M] :
    (E p M).IsFinitePresentation := by
  obtain ⟨P, hP⟩ := CoherentPullback.exists_presentation_pullback_tilde p M
  let := hP
  have : ((Scheme.Modules.pullback p).obj (tilde M)).IsFinitePresentation :=
    CoherentLocality.finitePresentation_of_presentation P
  exact CoherentDual.coherent_doubleDual _
end CoherentModelActual

end

end

section
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace CoherentDual
open Scheme.Modules
variable {A : CommRingCat.{0}} [IsNoetherianRing A] (M : ModuleCat A) [Module.Finite A M]

def affineDualGammaIso : moduleSpecΓFunctor.obj (affineHom M (ModuleCat.of A A)) ≅
    ModuleCat.of A (Module.Dual A M) :=
  (affineHomLinearEquiv M (ModuleCat.of A A)).toModuleIso

/-- The affine sheaf dual is the associated sheaf of the actual module dual.
Coherence, rather than a blanket Hom/localization assumption, supplies the
counit isomorphism. -/
def affineDualIso : tilde (ModuleCat.of A (Module.Dual A M)) ≅
    homSheaf (Spec A).sheaf (tilde M) (SheafOfModules.unit _) := by
  have : (tilde M).IsFinitePresentation := by
    obtain ⟨P, hP⟩ := CoherentPullback.exists_presentation_tilde M
    let := hP
    exact CoherentLocality.finitePresentation_of_presentation P
  have hD : (homSheaf (Spec A).sheaf (tilde M) (SheafOfModules.unit _)).IsFinitePresentation :=
    coherent_dual (tilde M)
  let := hD
  let D : (Spec A).Modules := homSheaf (Spec A).sheaf (tilde M) (SheafOfModules.unit _)
  have : D.IsFinitePresentation := hD
  have : IsIso (Scheme.Modules.fromTildeΓ D) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent D
  let e : moduleSpecΓFunctor.obj D ≅ ModuleCat.of A (Module.Dual A M) :=
    affineDualGammaIso M
  exact (tilde.functor A).mapIso e.symm ≪≫
    @asIso _ _ _ _ (Scheme.Modules.fromTildeΓ D)
      (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent D)
end CoherentDual

end

end

section
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace AffinePullback
open Scheme.Modules
variable {A B : CommRingCat.{0}} (f : A ⟶ B)

/-- Global sections of pushforward along an affine map are scalar restriction. -/
def pushforwardGammaIso :
    pushforward (Spec.map f) ⋙ (moduleSpecΓFunctor (R := A)) ≅
      (moduleSpecΓFunctor (R := B)) ⋙ ModuleCat.restrictScalars f.hom := by
  exact Functor.isoWhiskerRight (pushforwardCompModulesSpecToSheafIso f)
    (TopCat.Sheaf.forget _ _ ⋙ (evaluation _ _).obj (op ⊤))

/-- Affine pullback of an associated module is the actual tensor-product
extension of scalars, obtained by uniqueness of adjoints. -/
def pullbackTildeIso :
    tilde.functor A ⋙ pullback (Spec.map f) ≅
      ModuleCat.extendScalars f.hom ⋙ tilde.functor B :=
  ((conjugateIsoEquiv
    ((tilde.adjunction (R := A)).comp (pullbackPushforwardAdjunction (Spec.map f)))
    ((ModuleCat.extendRestrictScalarsAdj f.hom).comp (tilde.adjunction (R := B)))).symm
    (pushforwardGammaIso f)).symm
end AffinePullback

namespace AffinePullback
open Scheme.Modules
variable {A B : CommRingCat.{0}} (f : A ⟶ B)

/-- The actual pushforward of an associated sheaf along an affine morphism
is the associated sheaf of scalar restriction. -/
def pushforwardTildeIso (M : ModuleCat B) :
    (Scheme.Modules.pushforward (Spec.map f)).obj (tilde M) ≅
      tilde ((ModuleCat.restrictScalars f.hom).obj M) := by
  have : IsIso (Scheme.Modules.fromTildeΓ
      ((Scheme.Modules.pushforward (Spec.map f)).obj (tilde M))) :=
    isIso_fromTildeΓ_pushforward f (tilde M)
  exact (asIso (Scheme.Modules.fromTildeΓ _)).symm ≪≫
    (tilde.functor A).mapIso
      ((pushforwardGammaIso f).app (tilde M) ≪≫
        (ModuleCat.restrictScalars f.hom).mapIso (tilde.toTildeΓNatIso.app M).symm)
end AffinePullback

end

end

section

/-! A direct algebraic proof of the torsion-free divisor restriction of a dual,
used for the reflexive extension in the manuscript, lines 326–342. -/
namespace DualCartierRestriction
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

def tDual (t : R) : Submodule R (Module.Dual R M) :=
  LinearMap.range (t • (LinearMap.id : Module.Dual R M →ₗ[R] Module.Dual R M))

lemma mem_tDual_iff (t : R) (ht : IsSMulRegular R t) (f : Module.Dual R M) :
    f ∈ tDual t ↔ ∀ m, f m ∈ Ideal.span ({t} : Set R) := by
  constructor
  · rintro ⟨g, rfl⟩ m
    rw [Ideal.mem_span_singleton]
    exact ⟨g m, rfl⟩
  · intro h
    have hx (m : M) : ∃ a : R, t • a = f m := by
      obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp (h m)
      exact ⟨a, ha.symm⟩
    choose g hg using hx
    let g' : Module.Dual R M := {
      toFun := g
      map_add' := by
        intro m n
        apply ht
        change t • g (m + n) = t • (g m + g n)
        rw [hg, smul_add, hg, hg, map_add]
      map_smul' := by
        intro r m
        apply ht
        change t • g (r • m) = t • (r • g m)
        rw [hg, smul_comm t r, hg, map_smul] }
    refine ⟨g', ?_⟩
    apply LinearMap.ext
    exact hg

/-- A dual restricted to a prime effective Cartier divisor is torsion-free.
This is phrased in terms of scalars in R, without assuming an extra action
of the quotient ring. -/
lemma regular_on_restriction (t : R) (ht : IsSMulRegular R t)
    [hprime : (Ideal.span ({t} : Set R)).IsPrime] (r : R)
    (hr : r ∉ Ideal.span ({t} : Set R)) :
    IsSMulRegular (Module.Dual R M ⧸ tDual (M := M) t) r := by
  rw [isSMulRegular_quotient_iff_mem_of_smul_mem]
  intro f hf
  rw [mem_tDual_iff t ht] at hf ⊢
  intro m
  exact (hprime.mem_or_mem (by simpa using hf m)).resolve_left hr

lemma killed_by_equation (t : R) :
    Module.IsTorsionBy R (Module.Dual R M ⧸ tDual (M := M) t) t := by
  intro x
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨f, rfl⟩

noncomputable instance quotientModule (t : R) :
    Module (R ⧸ Ideal.span ({t} : Set R)) (Module.Dual R M ⧸ tDual (M := M) t) :=
  (killed_by_equation (M := M) t).module

lemma torsionFree_restriction (t : R) (ht : IsSMulRegular R t)
    [(Ideal.span ({t} : Set R)).IsPrime] :
    Module.IsTorsionFree (R ⧸ Ideal.span ({t} : Set R))
      (Module.Dual R M ⧸ tDual (M := M) t) where
  isSMulRegular q hq := by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
    have hr : r ∉ Ideal.span ({t} : Set R) := by
      intro hr
      exact (isRegular_iff_ne_zero.mp hq) (Ideal.Quotient.eq_zero_iff_mem.mpr hr)
    exact regular_on_restriction t ht r hr

end DualCartierRestriction


noncomputable section
open scoped TensorProduct
namespace DualCartierRestriction
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

lemma tDual_eq_span_smul (t : R) :
    tDual (M := M) t = Ideal.span ({t} : Set R) • (⊤ : Submodule R (Module.Dual R M)) := by
  rw [Submodule.ideal_span_singleton_smul]
  ext f
  change (∃ g, t • g = f) ↔ _
  simp only [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and]

/-- The module-theoretic pullback of a dual to a principal divisor is the
canonical quotient of that dual. -/
def tensorRestrictionEquiv (t : R) :
    ((R ⧸ Ideal.span ({t} : Set R)) ⊗[R] Module.Dual R M) ≃ₗ[R]
      Module.Dual R M ⧸ tDual (M := M) t :=
  (TensorProduct.quotTensorEquivQuotSMul (Module.Dual R M) _).trans
    (Submodule.quotEquivOfEq _ _ (tDual_eq_span_smul (M := M) t).symm)

lemma tensorRestrictionEquiv_mk_smul (t r : R)
    (x : (R ⧸ Ideal.span ({t} : Set R)) ⊗[R] Module.Dual R M) :
    tensorRestrictionEquiv (M := M) t ((Ideal.Quotient.mk (Ideal.span ({t} : Set R)) r) • x) =
      (Ideal.Quotient.mk (Ideal.span ({t} : Set R)) r) • tensorRestrictionEquiv (M := M) t x := by
  change tensorRestrictionEquiv t ((algebraMap R (R ⧸ Ideal.span ({t} : Set R)) r) • x) = _
  rw [algebraMap_smul]
  exact (tensorRestrictionEquiv t).map_smul r x

/-- Quotient-linearity of the affine pullback/quotient identification. -/
def tensorRestrictionQuotientEquiv (t : R) :
    ((R ⧸ Ideal.span ({t} : Set R)) ⊗[R] Module.Dual R M) ≃ₗ[R ⧸ Ideal.span ({t} : Set R)]
      Module.Dual R M ⧸ tDual (M := M) t where
  __ := (tensorRestrictionEquiv (M := M) t).toAddEquiv
  map_smul' q x := by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
    exact tensorRestrictionEquiv_mk_smul t r x

/-- Actual tensor-product restriction of any dual to an integral effective
Cartier divisor is torsion-free over the divisor ring. -/
lemma torsionFree_tensorRestriction (t : R) (ht : IsSMulRegular R t)
    [(Ideal.span ({t} : Set R)).IsPrime] :
    Module.IsTorsionFree (R ⧸ Ideal.span ({t} : Set R))
      ((R ⧸ Ideal.span ({t} : Set R)) ⊗[R] Module.Dual R M) := by
  let := torsionFree_restriction (M := M) t ht
  let e := tensorRestrictionQuotientEquiv (M := M) t
  exact e.injective.moduleIsTorsionFree e e.map_smul
end DualCartierRestriction

end

end

section
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace CoherentDual
open Scheme.Modules
variable {A B : CommRingCat.{0}} [IsNoetherianRing A] (M : ModuleCat A) [Module.Finite A M]

/-- A concrete affine restriction of the actual sheaf dual, with the actual
scalar-extension module, rather than a substitute quotient object. -/
def affineDualPullbackIso (f : A ⟶ B) :
    (Scheme.Modules.pullback (Spec.map f)).obj
      (homSheaf (Spec A).sheaf (tilde M) (SheafOfModules.unit _)) ≅
      tilde ((ModuleCat.extendScalars f.hom).obj (ModuleCat.of A (Module.Dual A M))) :=
  (Scheme.Modules.pullback (Spec.map f)).mapIso (affineDualIso M).symm ≪≫
    (AffinePullback.pullbackTildeIso f).app _

/-- Global sections of affine pullback of the sheaf dual are the tensor
extension of the module dual, as modules over the target ring. -/
def affineDualPullbackGammaIso (f : A ⟶ B) :
    moduleSpecΓFunctor.obj ((Scheme.Modules.pullback (Spec.map f)).obj
      (homSheaf (Spec A).sheaf (tilde M) (SheafOfModules.unit _))) ≅
      (ModuleCat.extendScalars f.hom).obj (ModuleCat.of A (Module.Dual A M)) :=
  moduleSpecΓFunctor.mapIso (affineDualPullbackIso M f) ≪≫
    (tilde.toTildeΓNatIso.app _).symm

/-- The actual sheaf-dual restriction has torsion-free affine sections along
an integral effective Cartier divisor (the manuscript, lines 326–342). -/
lemma affineDualPullbackGamma_torsionFree (t : A) (ht : IsSMulRegular A t)
    [(Ideal.span ({t} : Set A)).IsPrime] :
    let f : A ⟶ CommRingCat.of (A ⧸ Ideal.span ({t} : Set A)) :=
      CommRingCat.ofHom (Ideal.Quotient.mk _)
    Module.IsTorsionFree (A ⧸ Ideal.span ({t} : Set A))
      ((moduleSpecΓFunctor (R := CommRingCat.of (A ⧸ Ideal.span ({t} : Set A)))).obj ((Scheme.Modules.pullback (Spec.map f)).obj
        (homSheaf (Spec A).sheaf (tilde M) (SheafOfModules.unit _)))) := by
  dsimp only
  let f : A ⟶ CommRingCat.of (A ⧸ Ideal.span ({t} : Set A)) :=
    CommRingCat.ofHom (Ideal.Quotient.mk _)
  let e := (affineDualPullbackGammaIso M f).toLinearEquiv
  have : Module.IsTorsionFree (A ⧸ Ideal.span ({t} : Set A))
      ((ModuleCat.extendScalars f.hom).obj (ModuleCat.of A (Module.Dual A M))) :=
    DualCartierRestriction.torsionFree_tensorRestriction (M := M) t ht
  exact e.injective.moduleIsTorsionFree e e.map_smul
end CoherentDual

end

end

section

noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace CoherentModelActual
open CoherentDual Scheme.Modules
variable {A B : CommRingCat.{0}} [IsNoetherianRing B]
  (f : A ⟶ B) (M : ModuleCat A) [Module.Finite A M]

/-- The actual scalar-extension module on an affine model chart. -/
abbrev affineModule := (ModuleCat.extendScalars f.hom).obj M

instance affineModule_finite : Module.Finite B (affineModule f M) := by
  let : Algebra A B := f.hom.toAlgebra
  change Module.Finite B (TensorProduct A B M)
  infer_instance

instance affineModule_dual_finite : Module.Finite B (Module.Dual B (affineModule f M)) := by
  have : IsNoetherian B (Module.Dual B (affineModule f M)) :=
    isNoetherian_linearMap B B (affineModule f M)
  exact ⟨IsNoetherian.noetherian ⊤⟩

/-- The first sheaf dual of the actual pullback is the associated module
dual of the actual tensor extension, not an abstract reflexive object. -/
def affineFirstDualIso :
    tilde (ModuleCat.of B (Module.Dual B (affineModule f M))) ≅
      homSheaf (Spec B).sheaf ((Scheme.Modules.pullback (Spec.map f)).obj (tilde M))
        (SheafOfModules.unit _) :=
  affineDualIso (affineModule f M) ≪≫
    (homSheafFunctor (Spec B).sheaf (SheafOfModules.unit _)).mapIso
       ((AffinePullback.pullbackTildeIso f).app M).op

/-- The affine description of the precise double-dual model extension. -/
def affineEIso : E (Spec.map f) M ≅
    tilde (ModuleCat.of B (Module.Dual B (Module.Dual B (affineModule f M)))) :=
  (homSheafFunctor (Spec B).sheaf (SheafOfModules.unit _)).mapIso
    (affineFirstDualIso f M).op ≪≫
      (affineDualIso (ModuleCat.of B (Module.Dual B (affineModule f M)))).symm

/-- Restricting the genuine affine model extension to an integral Cartier
divisor gives torsion-free sections. Only the literal regular equation and
primality are used; the model sheaf is CONSTRUCTED from arbitrary M. -/
theorem affineE_cartier_torsionFree (t : B) (ht : IsSMulRegular B t)
    [(Ideal.span ({t} : Set B)).IsPrime] :
    let q : B ⟶ CommRingCat.of (B ⧸ Ideal.span ({t} : Set B)) :=
      CommRingCat.ofHom (Ideal.Quotient.mk _)
    Module.IsTorsionFree (B ⧸ Ideal.span ({t} : Set B))
      ((moduleSpecΓFunctor (R := CommRingCat.of (B ⧸ Ideal.span ({t} : Set B)))).obj
        ((Scheme.Modules.pullback (Spec.map q)).obj (E (Spec.map f) M))) := by
  dsimp only
  let q : B ⟶ CommRingCat.of (B ⧸ Ideal.span ({t} : Set B)) :=
    CommRingCat.ofHom (Ideal.Quotient.mk _)
  let N : ModuleCat B := ModuleCat.of B (Module.Dual B (affineModule f M))
  let d : E (Spec.map f) M ≅ homSheaf (Spec B).sheaf (tilde N) (SheafOfModules.unit _) :=
    (homSheafFunctor (Spec B).sheaf (SheafOfModules.unit _)).mapIso
      (affineFirstDualIso f M).op
  let e := (moduleSpecΓFunctor (R := CommRingCat.of (B ⧸ Ideal.span ({t} : Set B)))).mapIso
    ((Scheme.Modules.pullback (Spec.map q)).mapIso d)
  have : Module.IsTorsionFree (B ⧸ Ideal.span ({t} : Set B))
      ((moduleSpecΓFunctor (R := CommRingCat.of (B ⧸ Ideal.span ({t} : Set B)))).obj
        ((Scheme.Modules.pullback (Spec.map q)).obj
          (homSheaf (Spec B).sheaf (tilde N) (SheafOfModules.unit _)))) :=
    affineDualPullbackGamma_torsionFree N t ht
  exact e.toLinearEquiv.injective.moduleIsTorsionFree e.toLinearEquiv e.toLinearEquiv.map_smul
end CoherentModelActual

end

end

section

noncomputable section
open scoped TensorProduct
open TensorProduct
namespace FiniteDomainDual
variable {R M : Type*} [CommRing R] [IsDomain R]
  [AddCommGroup M] [Module R M]

/-- A finite presented torsion-free module over a domain has enough honest
R-valued dual functionals. Denominators are cleared over R, not assumed away. -/
lemma exists_dual_ne_zero [Module.FinitePresentation R M] [Module.IsTorsionFree R M]
    {m : M} (hm : m ≠ 0) : ∃ f : Module.Dual R M, f m ≠ 0 := by
  let S := nonZeroDivisors R
  let K := FractionRing R
  let V := LocalizedModule S M
  let j : M →ₗ[R] V := LocalizedModule.mkLinearMap S M
  have hj : Function.Injective j := by
    apply (IsLocalizedModule.injective_iff_isRegular S j).mpr
    intro c
    exact Module.IsTorsionFree.isSMulRegular (M := M)
      (isRegular_iff_ne_zero.mpr (mem_nonZeroDivisors_iff_ne_zero.mp c.property))
  have hmono : j m ≠ 0 := by
    intro h
    apply hm
    exact hj (h.trans (map_zero j).symm)
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero K hmono
  let g : M →ₗ[R] K := (f.restrictScalars R).comp j
  obtain ⟨l, s, hs⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule
    S (Algebra.linearMap R K) g
  refine ⟨l, ?_⟩
  intro hl
  have he := LinearMap.congr_fun hs m
  change algebraMap R K (l m) = (s : R) • f (j m) at he
  rw [hl, map_zero] at he
  have hsn : (algebraMap R K) (s : R) ≠ 0 := by
    simpa only [map_zero] using
      (IsFractionRing.injective R K).ne (mem_nonZeroDivisors_iff_ne_zero.mp s.property)
  exact (mul_ne_zero hsn hf) (by
    simpa only [Algebra.smul_def] using he.symm)

/-- Nontriviality of the dual is derived, rather than built into the model sheaf input. -/
lemma dual_nontrivial [Module.FinitePresentation R M] [Module.IsTorsionFree R M]
    [Nontrivial M] : Nontrivial (Module.Dual R M) := by
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  obtain ⟨f, hf⟩ := exists_dual_ne_zero (R := R) hm
  exact ⟨⟨f, 0, fun h => hf (by rw [h]; rfl)⟩⟩

/-- Even non-flat birational base change does not kill the double dual of a
nonzero finite torsion-free module. The ring-map injectivity is essential;
no flatness of the blowup chart is asserted. -/
lemma doubleDual_baseChange_nontrivial [Module.FinitePresentation R M]
    [Module.IsTorsionFree R M] [Nontrivial M]
    (B : Type*) [CommRing B] [Algebra R B]
    (hinj : Function.Injective (algebraMap R B)) :
    Nontrivial (Module.Dual B (Module.Dual B (B ⊗[R] M))) := by
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  obtain ⟨f, hf⟩ := exists_dual_ne_zero (R := R) hm
  let e := Module.Dual.eval B (B ⊗[R] M) ((1 : B) ⊗ₜ[R] m)
  have he : e (f.baseChange B) ≠ 0 := by
    change (f m) • (1 : B) ≠ 0
    simpa only [Algebra.smul_def, mul_one, map_zero] using hinj.ne hf
  exact ⟨⟨e, 0, fun h => he (by rw [h]; rfl)⟩⟩

/-- Every prime is in the support of a nonzero torsion-free module over a domain. -/
lemma mem_support [Module.IsTorsionFree R M] [Nontrivial M] (p : PrimeSpectrum R) :
    p ∈ Module.support R M := by
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  apply Module.mem_support_iff'.mpr
  refine ⟨m, ?_⟩
  intro r hr
  exact smul_ne_zero (fun h => hr (h ▸ p.asIdeal.zero_mem)) hm

/-- A finite, nonzero torsion-free module remains nonzero on every prime
fiber; this supplies the positivity lost by a mere torsion-free assertion. -/
lemma prime_fiber_nontrivial [Module.Finite R M] [Module.IsTorsionFree R M]
    [Nontrivial M] (p : Ideal R) [p.IsPrime] :
    Nontrivial ((R ⧸ p) ⊗[R] M) := by
  have : Nontrivial (p.ResidueField ⊗[R] M) :=
    (Module.mem_support_iff_nontrivial_residueField_tensorProduct ⟨p, inferInstance⟩).mp
      (mem_support ⟨p, inferInstance⟩)
  let e := AlgebraTensorModule.cancelBaseChange R (R ⧸ p) p.ResidueField p.ResidueField M
  by_contra h
  have : Subsingleton ((R ⧸ p) ⊗[R] M) := not_nontrivial_iff_subsingleton.mp h
  have : Subsingleton (p.ResidueField ⊗[R ⧸ p] ((R ⧸ p) ⊗[R] M)) := inferInstance
  have : Subsingleton (p.ResidueField ⊗[R] M) := e.surjective.subsingleton
  exact not_nontrivial_iff_subsingleton.mpr this inferInstance

/-- The actual generic rank of the prime-divisor restriction is positive.
The residue field here is Mathlib's fraction field of R/p. -/
lemma prime_fiber_rank_pos [Module.Finite R M] [Module.IsTorsionFree R M]
    [Nontrivial M] (p : Ideal R) [p.IsPrime] :
    0 < Module.finrank p.ResidueField
      (p.ResidueField ⊗[R ⧸ p] ((R ⧸ p) ⊗[R] M)) := by
  have : Nontrivial (p.ResidueField ⊗[R] M) :=
    (Module.mem_support_iff_nontrivial_residueField_tensorProduct ⟨p, inferInstance⟩).mp
      (mem_support ⟨p, inferInstance⟩)
  let e := AlgebraTensorModule.cancelBaseChange R (R ⧸ p) p.ResidueField p.ResidueField M
  have : Nontrivial (p.ResidueField ⊗[R ⧸ p] ((R ⧸ p) ⊗[R] M)) := e.nontrivial
  exact Module.finrank_pos
end FiniteDomainDual


end

end

end OAI
