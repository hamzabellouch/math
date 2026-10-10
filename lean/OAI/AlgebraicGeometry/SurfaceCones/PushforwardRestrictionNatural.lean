import OAI.AlgebraicGeometry.SurfaceCones.CMPuncture

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace CoherentBaseChange
open Scheme.Modules
/-- The open basechange comparison is natural in the module sheaf. -/
def pushforwardRestrictNatIso {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens) :
    pushforward f ⋙ restrictFunctor U.ι ≅
      restrictFunctor (f ⁻¹ᵁ U).ι ⋙ pushforward (f ∣_ U) := by
  refine NatIso.ofComponents (pushforwardRestrictIso f U) ?_
  intro M N g
  apply Scheme.Modules.hom_ext
  intro V
  apply AddCommGrpCat.ext
  intro x
  change (g.mapPresheaf.app (op (f ⁻¹ᵁ (U.ι ''ᵁ V))) ≫
      N.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V)).op) x =
    (M.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V)).op ≫
      g.mapPresheaf.app (op ((f ⁻¹ᵁ U).ι ''ᵁ ((f ∣_ U) ⁻¹ᵁ V)))) x
  exact congrArg (fun z => z x)
    (g.mapPresheaf.naturality (eqToHom (image_morphismRestrict_preimage f U V)).op).symm
end CoherentBaseChange

end

noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace CoherentGlobal
open Scheme.Modules
lemma exact_pushforward_iso {X Y : Scheme.{0}} (e : X ≅ Y)
    (S : ShortComplex X.Modules) (hS : S.Exact) :
    (S.map (pushforward e.hom)).Exact := by
  have : PreservesFiniteLimits (restrictFunctor e.inv) :=
    CoherentRestriction.preservesFiniteLimits e.inv
  exact ShortComplex.exact_of_iso (S.mapNatIso (pushforwardIsoRestrict e).symm)
    (hS.map (restrictFunctor e.inv))

/-- Exactness of affine pushforward on coherent sheaves, for affine schemes not assumed to be
definitionally spectra. -/
lemma exact_pushforward_affine {X Y : Scheme.{0}} [IsAffine X] [IsAffine Y]
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [IsFinite f]
    (S : ShortComplex X.Modules)
    [S.X₁.IsFinitePresentation] [S.X₂.IsFinitePresentation] [S.X₃.IsFinitePresentation]
    (hS : S.Exact) : (S.map (pushforward f)).Exact := by
  have : IsNoetherianRing Γ(Y, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top Y⟩
  have : ((S.map (pushforward X.isoSpec.hom)).X₁).IsQuasicoherent := by
    let := coherent_pushforward_iso X.isoSpec S.X₁
    exact (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
      ((pushforward X.isoSpec.hom).obj S.X₁)).choose.isQuasicoherent
  have : ((S.map (pushforward X.isoSpec.hom)).X₂).IsQuasicoherent := by
    let := coherent_pushforward_iso X.isoSpec S.X₂
    exact (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
      ((pushforward X.isoSpec.hom).obj S.X₂)).choose.isQuasicoherent
  have : ((S.map (pushforward X.isoSpec.hom)).X₃).IsQuasicoherent := by
    let := coherent_pushforward_iso X.isoSpec S.X₃
    exact (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
      ((pushforward X.isoSpec.hom).obj S.X₃)).choose.isQuasicoherent
  have h1 := exact_pushforward_iso X.isoSpec S hS
  have h2 := exact_affinePushforward f.appTop (S.map (pushforward X.isoSpec.hom)) h1
  have h3 := exact_pushforward_iso Y.isoSpec.symm _ h2
  have he : X.isoSpec.hom ≫ Spec.map f.appTop ≫ Y.isoSpec.inv = f := by
    rw [← Category.assoc, Scheme.isoSpec_hom_naturality]
    simp
  let e1 := (S.map (pushforward X.isoSpec.hom)).mapNatIso
    (pushforwardComp (Spec.map f.appTop) Y.isoSpec.inv)
  let e2 := S.mapNatIso (pushforwardComp X.isoSpec.hom
    (Spec.map f.appTop ≫ Y.isoSpec.inv))
  let e3 := S.mapNatIso (pushforwardCongr he)
  exact ShortComplex.exact_of_iso (e1 ≪≫ e2 ≪≫ e3) h3

/-- Finite pushforward is exact on coherent sheaves, not on arbitrary sheaves. -/
lemma exact_pushforward {X Y : Scheme.{0}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsFinite f] (S : ShortComplex X.Modules)
    [S.X₁.IsFinitePresentation] [S.X₂.IsFinitePresentation] [S.X₃.IsFinitePresentation]
    (hS : S.Exact) : (S.map (pushforward f)).Exact := by
  apply exact_of_affine_restrict
  intro U
  have : IsAffine U.1.toScheme := U.2
  have : IsAffine (f ⁻¹ᵁ U.1).toScheme := U.2.preimage f
  have : PreservesFiniteLimits (restrictFunctor (f ⁻¹ᵁ U.1).ι) :=
    CoherentRestriction.preservesFiniteLimits _
  have : ((S.map (restrictFunctor (f ⁻¹ᵁ U.1).ι)).X₁).IsFinitePresentation :=
    coherent_restrict _ _
  have : ((S.map (restrictFunctor (f ⁻¹ᵁ U.1).ι)).X₂).IsFinitePresentation :=
    coherent_restrict _ _
  have : ((S.map (restrictFunctor (f ⁻¹ᵁ U.1).ι)).X₃).IsFinitePresentation :=
    coherent_restrict _ _
  have h := exact_pushforward_affine (f ∣_ U.1) _
    (hS.map (restrictFunctor (f ⁻¹ᵁ U.1).ι))
  exact ShortComplex.exact_of_iso
    (S.mapNatIso (CoherentBaseChange.pushforwardRestrictNatIso f U.1).symm) h
end CoherentGlobal

end

noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace CoherentGlobal
open Scheme.Modules

/-- Inclusion of the coherent category into all structure-sheaf modules. -/
abbrev cohInclusion (X : Scheme.{0}) : Coh X ⥤ X.Modules :=
  (SheafOfModules.isFinitePresentation X.ringCatSheaf).ι

instance cohInclusion_additive (X : Scheme.{0}) : (cohInclusion X).Additive where
  map_add := by intros; rfl

instance cohInclusion_faithful (X : Scheme.{0}) : (cohInclusion X).Faithful :=
  (SheafOfModules.isFinitePresentation X.ringCatSheaf).fullyFaithfulι.faithful

instance cohInclusion_kernels (X : Scheme.{0}) [IsLocallyNoetherian X]
    {M N : Coh X} (g : M ⟶ N) :
    PreservesLimit (parallelPair g 0) (cohInclusion X) :=
  (SheafOfModules.isFinitePresentation X.ringCatSheaf).preservesKernels_ι g

instance cohInclusion_cokernels (X : Scheme.{0}) [IsLocallyNoetherian X]
    {M N : Coh X} (g : M ⟶ N) :
    PreservesColimit (parallelPair g 0) (cohInclusion X) :=
  (SheafOfModules.isFinitePresentation X.ringCatSheaf).preservesCokernels_ι g

instance cohInclusion_limits (X : Scheme.{0}) [IsLocallyNoetherian X] :
    PreservesFiniteLimits (cohInclusion X) :=
  Functor.preservesFiniteLimits_of_preservesKernels (cohInclusion X)

instance cohInclusion_colimits (X : Scheme.{0}) [IsLocallyNoetherian X] :
    PreservesFiniteColimits (cohInclusion X) :=
  Functor.preservesFiniteColimits_of_preservesCokernels (cohInclusion X)

/-- Finite pushforward as a functor of coherent categories. -/
def cohPushforward {X Y : Scheme.{0}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsFinite f] : Coh X ⥤ Coh Y :=
  (SheafOfModules.isFinitePresentation Y.ringCatSheaf).lift
    (cohInclusion X ⋙ pushforward f) (fun M => by
      let := M.property
      exact coherent_pushforward f M.obj)

instance cohPushforward_additive {X Y : Scheme.{0}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsFinite f] : (cohPushforward f).Additive where
  map_add := by
    intros
    apply ObjectProperty.hom_ext
    exact (pushforward f).map_add

lemma exact_cohPushforward {X Y : Scheme.{0}} [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [IsFinite f]
    (S : ShortComplex (Coh X)) (hS : S.Exact) : (S.map (cohPushforward f)).Exact := by
  apply ((S.map (cohPushforward f)).exact_map_iff_of_faithful (cohInclusion Y)).mp
  have hX := hS.map (cohInclusion X)
  have : (S.map (cohInclusion X)).X₁.IsFinitePresentation := S.X₁.property
  have : (S.map (cohInclusion X)).X₂.IsFinitePresentation := S.X₂.property
  have : (S.map (cohInclusion X)).X₃.IsFinitePresentation := S.X₃.property
  exact exact_pushforward f (S.map (cohInclusion X)) hX

instance cohPushforward_preservesHomology {X Y : Scheme.{0}} [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [IsFinite f] :
    (cohPushforward f).PreservesHomology :=
  Functor.preservesHomology_of_map_exact _ (exact_cohPushforward f)

instance cohPushforward_preservesFiniteLimits {X Y : Scheme.{0}} [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [IsFinite f] :
    PreservesFiniteLimits (cohPushforward f) :=
  (cohPushforward f).preservesFiniteLimits_of_preservesHomology

instance cohPushforward_preservesFiniteColimits {X Y : Scheme.{0}} [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [IsFinite f] :
    PreservesFiniteColimits (cohPushforward f) :=
  (cohPushforward f).preservesFiniteColimits_of_preservesHomology
end CoherentGlobal

end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace SheafTorsion
universe u v

/-- Torsion freedom is closed under left-exact module extensions. -/
lemma module_extension {R : Type u} [CommRing R]
    (S : ShortComplex (ModuleCat.{v} R)) (he : S.Exact) [Mono S.f]
    [Module.IsTorsionFree R S.X₁] [Module.IsTorsionFree R S.X₃] :
    Module.IsTorsionFree R S.X₂ where
  isSMulRegular r hr := by
    intro x y hxy
    have hg : S.g (x - y) = 0 := by
      apply (hr.smul_eq_zero_iff_right).mp
      simpa only [map_sub, map_smul, smul_sub, sub_eq_zero] using congrArg S.g hxy
    obtain ⟨z, hz⟩ := (S.moduleCat_exact_iff.mp he) (x - y) hg
    have hf : Function.Injective S.f := (ModuleCat.mono_iff_injective S.f).mp inferInstance
    change r • x = r • y at hxy
    have hsz : r • z = 0 := by
      apply hf
      rw [map_smul, hz, smul_sub, hxy, sub_self, map_zero]
    have hzero : z = 0 := hr.smul_eq_zero_iff_right.mp hsz
    have : x - y = 0 := by rw [← hz, hzero, map_zero]
    exact sub_eq_zero.mp this

/-- Every section module of a module-sheaf subobject of a torsion-free sheaf is torsion-free. No
local freeness is assumed. -/
lemma subobject {X : Scheme.{0}} {M N : X.Modules} (f : M ⟶ N) [Mono f]
    (hN : ∀ U, @Module.IsTorsionFree (X.sheaf.obj.obj U) (N.val.obj U) _ _
      (N.val.obj U).isModule)
    (U : X.Opensᵒᵖ) : @Module.IsTorsionFree (X.sheaf.obj.obj U) (M.val.obj U) _ _
      (M.val.obj U).isModule := by
  let : Module (X.sheaf.obj.obj U) (M.val.obj U) := (M.val.obj U).isModule
  let : Module (X.sheaf.obj.obj U) (N.val.obj U) := (N.val.obj U).isModule
  let := hN U
  let F : X.Modules ⥤ ModuleCat.{0} (X.ringCatSheaf.obj.obj U) :=
    SheafOfModules.evaluation X.ringCatSheaf U
  have : PreservesFiniteLimits F := SheafOfModules.Finite.evaluationPreservesFiniteLimits X.ringCatSheaf U
  have : Mono (F.map f) := inferInstance
  have hf : Function.Injective (f.val.app U) :=
    (ModuleCat.mono_iff_injective _).mp this
  exact @Function.Injective.moduleIsTorsionFree
    (X.sheaf.obj.obj U) (M.val.obj U) (N.val.obj U) _ _ (M.val.obj U).isModule
    _ (N.val.obj U).isModule (hN U) (f.val.app U) hf
    (fun r m => (f.val.app U).hom.map_smul r m)

/-- Sectionwise torsion freedom is closed under left-exact sheaf extensions: sections preserve the
kernel, even though they need not preserve epimorphisms. -/
lemma extension {X : Scheme.{0}} (S : ShortComplex X.Modules)
    (he : S.Exact) [Mono S.f]
    (h₁ : ∀ U, @Module.IsTorsionFree (X.sheaf.obj.obj U) (S.X₁.val.obj U) _ _
      (S.X₁.val.obj U).isModule)
    (h₃ : ∀ U, @Module.IsTorsionFree (X.sheaf.obj.obj U) (S.X₃.val.obj U) _ _
      (S.X₃.val.obj U).isModule)
    (U : X.Opensᵒᵖ) : @Module.IsTorsionFree (X.sheaf.obj.obj U) (S.X₂.val.obj U) _ _
      (S.X₂.val.obj U).isModule := by
  let F : X.Modules ⥤ ModuleCat.{0} (X.ringCatSheaf.obj.obj U) :=
    SheafOfModules.evaluation X.ringCatSheaf U
  have : F.Additive := ⟨by intros; rfl⟩
  have : PreservesFiniteLimits F := SheafOfModules.Finite.evaluationPreservesFiniteLimits X.ringCatSheaf U
  let _ : CommRing (X.ringCatSheaf.obj.obj U) :=
    inferInstanceAs (CommRing (X.sheaf.obj.obj U))
  have hmap : (S.map F).Exact :=
    he.map_of_mono_of_preservesKernel F inferInstance inferInstance
  have : Module.IsTorsionFree (X.ringCatSheaf.obj.obj U) (S.map F).X₁ := h₁ U
  have : Module.IsTorsionFree (X.ringCatSheaf.obj.obj U) (S.map F).X₃ := h₃ U
  have : Mono (S.map F).f := by change Mono (F.map S.f); infer_instance
  exact module_extension (S.map F) hmap

lemma coherent_extension {X : Scheme.{0}} [IsLocallyNoetherian X]
    (S : ShortComplex (CoherentGlobal.Coh X)) (he : S.Exact) [Mono S.f]
    (h₁ : ∀ U, @Module.IsTorsionFree (X.sheaf.obj.obj U) (S.X₁.obj.val.obj U) _ _
      (S.X₁.obj.val.obj U).isModule)
    (h₃ : ∀ U, @Module.IsTorsionFree (X.sheaf.obj.obj U) (S.X₃.obj.val.obj U) _ _
      (S.X₃.obj.val.obj U).isModule)
    (U : X.Opensᵒᵖ) : @Module.IsTorsionFree (X.sheaf.obj.obj U) (S.X₂.obj.val.obj U) _ _
      (S.X₂.obj.val.obj U).isModule := by
  have : Mono (S.map (CoherentGlobal.cohInclusion X)).f := by
    change Mono ((CoherentGlobal.cohInclusion X).map S.f)
    infer_instance
  exact extension (S.map (CoherentGlobal.cohInclusion X)) (he.map _) h₁ h₃ U
end SheafTorsion

end

noncomputable section
open TensorProduct
namespace DualCartierRestriction
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The canonical dual base-change map, without any false freeness assumption. -/
def dualBaseChangeMap (A : Type*) [CommRing A] [Algebra R A] :
    A ⊗[R] Module.Dual R M →ₗ[A] Module.Dual A (A ⊗[R] M) :=
  AlgebraTensorModule.lift {
    toFun a := a • Module.Dual.baseChange A
    map_add' a b := by simp [add_smul]
    map_smul' a b := by simp [smul_smul] }

@[simp]
lemma dualBaseChangeMap_tmul (A : Type*) [CommRing A] [Algebra R A]
    (a b : A) (f : Module.Dual R M) (m : M) :
    dualBaseChangeMap A (a ⊗ₜ[R] f) (b ⊗ₜ[R] m) = a • (f m • b) := rfl

/-- Scalar extension along a quotient is generated by tensors with first coordinate one, even when
the module is not free. -/
lemma quotient_one_tmul_surjective (I : Ideal R) :
    Function.Surjective (fun m : M => (1 : R ⧸ I) ⊗ₜ[R] m) := by
  intro z
  let e := TensorProduct.quotTensorEquivQuotSMul M I
  obtain ⟨m, hm⟩ := Submodule.Quotient.mk_surjective (I • (⊤ : Submodule R M)) (e z)
  exact ⟨m, e.injective ((TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul I m).trans hm)⟩

/-- Restriction of a dual to any effective principal Cartier divisor injects into the dual of the
restricted module. The divisor need not be smooth for this algebraic assertion. -/
lemma dualBaseChangeMap_injective (t : R) (ht : IsSMulRegular R t) :
    Function.Injective (dualBaseChangeMap (R := R) (M := M) (R ⧸ Ideal.span ({t} : Set R))) := by
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro z hz
  obtain ⟨f, rfl⟩ := quotient_one_tmul_surjective (M := Module.Dual R M)
    (Ideal.span ({t} : Set R)) z
  have hf : ∀ m, f m ∈ Ideal.span ({t} : Set R) := by
    intro m
    have h := congrArg (fun g : Module.Dual (R ⧸ Ideal.span ({t} : Set R))
      ((R ⧸ Ideal.span ({t} : Set R)) ⊗[R] M) => g (1 ⊗ₜ[R] m)) hz
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa [Algebra.smul_def] using h
  obtain ⟨g, hg⟩ := (mem_tDual_iff t ht f).mpr hf
  change t • g = f at hg
  rw [← hg]
  change (1 : R ⧸ Ideal.span ({t} : Set R)) ⊗ₜ[R] (t • g) = 0
  rw [← TensorProduct.smul_tmul]
  have heq : t • (1 : R ⧸ Ideal.span ({t} : Set R)) = 0 := by
    simp only [Algebra.smul_def, mul_one]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton t))
  rw [heq, TensorProduct.zero_tmul]
end DualCartierRestriction

end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace CoherentDual
open Scheme.Modules

private def dualBaseChangeMorphism {A B : CommRingCat.{0}} (φ : A ⟶ B) (M : ModuleCat A) :
    (ModuleCat.extendScalars φ.hom).obj (ModuleCat.of A (Module.Dual A M)) ⟶
      ModuleCat.of B (Module.Dual B ((ModuleCat.extendScalars φ.hom).obj M)) := by
  let : Algebra A B := φ.hom.toAlgebra
  let X := (ModuleCat.extendScalars φ.hom).obj (ModuleCat.of A (Module.Dual A M))
  let Y := ModuleCat.of B (Module.Dual B ((ModuleCat.extendScalars φ.hom).obj M))
  exact @ModuleCat.ofHom B _ X Y X.isAddCommGroup X.isModule Y.isAddCommGroup Y.isModule
    (DualCartierRestriction.dualBaseChangeMap (R := A) (M := M) B)

variable {A : CommRingCat.{0}} [IsNoetherianRing A]
  (M : ModuleCat A) [Module.Finite A M]
  (t : A) (ht : IsSMulRegular A t)

abbrev principalQuotient : CommRingCat.{0} := CommRingCat.of (A ⧸ Ideal.span ({t} : Set A))
abbrev principalMap : A ⟶ principalQuotient t := CommRingCat.ofHom (Ideal.Quotient.mk _)

instance principalTensor_finite :
    Module.Finite (principalQuotient t)
      ((ModuleCat.extendScalars (principalMap t).hom).obj M) := by
  change Module.Finite (principalQuotient t) (TensorProduct A (principalQuotient t) M)
  infer_instance

/-- On an affine Cartier chart, the restriction of the sheaf dual embeds in the dual of the
genuinely scalar-extended module. -/
def principalDualInjection :
    (Scheme.Modules.pullback (Spec.map (principalMap t))).obj
      (homSheaf (Spec A).sheaf (tilde M) (SheafOfModules.unit _)) ⟶
    homSheaf (Spec (principalQuotient t)).sheaf
      (tilde ((ModuleCat.extendScalars (principalMap t).hom).obj M))
      (SheafOfModules.unit _) :=
  (Scheme.Modules.pullback (Spec.map (principalMap t))).map (affineDualIso M).inv ≫
    ((AffinePullback.pullbackTildeIso (principalMap t)).app
      (ModuleCat.of A (Module.Dual A M))).hom ≫
    (tilde.functor (principalQuotient t)).map
      (dualBaseChangeMorphism (principalMap t) M) ≫
    (affineDualIso ((ModuleCat.extendScalars (principalMap t).hom).obj M)).hom

include ht in
lemma principalDualInjection_mono : Mono (principalDualInjection M t) := by
  have hdual : Mono (dualBaseChangeMorphism (principalMap t) M) :=
    (ModuleCat.mono_iff_injective _).mpr
      (DualCartierRestriction.dualBaseChangeMap_injective t ht)
  let a := (Scheme.Modules.pullback (Spec.map (principalMap t))).map (affineDualIso M).inv
  let b := ((AffinePullback.pullbackTildeIso (principalMap t)).app
    (ModuleCat.of A (Module.Dual A M))).hom
  let c := (tilde.functor (principalQuotient t)).map
    (dualBaseChangeMorphism (principalMap t) M)
  let d := (affineDualIso ((ModuleCat.extendScalars (principalMap t).hom).obj M)).hom
  have : IsIso a := ((Scheme.Modules.pullback _).mapIso (affineDualIso M).symm).isIso_hom
  have : IsIso b := ((AffinePullback.pullbackTildeIso _).app
    (ModuleCat.of A (Module.Dual A M))).isIso_hom
  have : Mono c :=
    (CoherentExactAffine.preservesMonomorphisms (R := principalQuotient t)).preserves _
  have : IsIso d := (affineDualIso _).isIso_hom
  change Mono (a ≫ b ≫ c ≫ d)
  exact mono_comp' (IsIso.mono_of_iso a) (mono_comp' (IsIso.mono_of_iso b) (mono_comp' ‹Mono c› (IsIso.mono_of_iso d)))

include ht in
/-- Restriction of a sheaf dual to an integral principal Cartier divisor is torsion-free. -/
lemma principalDual_restriction_torsionFree
    [(Ideal.span ({t} : Set A)).IsPrime]
    (U : (Spec (principalQuotient t)).Opensᵒᵖ) :
    @Module.IsTorsionFree ((Spec (principalQuotient t)).sheaf.obj.obj U)
      (((Scheme.Modules.pullback (Spec.map (principalMap t))).obj
        (homSheaf (Spec A).sheaf (tilde M) (SheafOfModules.unit _))).val.obj U) _ _
      ((((Scheme.Modules.pullback (Spec.map (principalMap t))).obj
        (homSheaf (Spec A).sheaf (tilde M) (SheafOfModules.unit _))).val.obj U).isModule) := by
  have : Mono (principalDualInjection M t) := principalDualInjection_mono M t ht
  exact SheafTorsion.subobject (principalDualInjection M t)
    (fun V => dual_sections_torsionFree _ V.unop) U
end CoherentDual

end

noncomputable section
open TensorProduct
namespace DualCartierRestriction
variable {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M]

/-- Surjective scalar extension is generated by tensors with first coordinate one. No freeness,
finite generation or chosen presentation is needed. -/
lemma surjective_one_tmul (h : Function.Surjective (algebraMap R A)) :
    Function.Surjective (fun m : M => (1 : A) ⊗ₜ[R] m) := by
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul a m =>
      obtain ⟨r, rfl⟩ := h a
      refine ⟨r • m, ?_⟩
      change (1 : A) ⊗ₜ[R] (r • m) = algebraMap R A r ⊗ₜ[R] m
      rw [← TensorProduct.smul_tmul]
      simp [Algebra.smul_def]
  | add x y hx hy =>
      obtain ⟨m, rfl⟩ := hx
      obtain ⟨n, rfl⟩ := hy
      exact ⟨m + n, TensorProduct.tmul_add _ _ _⟩

/-- Canonical dual specialization is injective for any surjective ring morphism whose kernel is
generated by a regular element. This avoids identifying the target ring definitionally with a
chosen quotient. -/
lemma dualBaseChangeMap_injective_of_surjective
    (h : Function.Surjective (algebraMap R A)) (t : R) (ht : IsSMulRegular R t)
    (hker : RingHom.ker (algebraMap R A) = Ideal.span ({t} : Set R)) :
    Function.Injective (dualBaseChangeMap (R := R) (M := M) A) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro z hz
  obtain ⟨f, rfl⟩ := surjective_one_tmul (M := Module.Dual R M) h z
  have hf : ∀ m, f m ∈ Ideal.span ({t} : Set R) := by
    intro m
    rw [← hker]
    have hh := congrArg (fun g : Module.Dual A (A ⊗[R] M) => g (1 ⊗ₜ[R] m)) hz
    change algebraMap R A (f m) = 0
    simpa [Algebra.smul_def] using hh
  obtain ⟨g, hg⟩ := (mem_tDual_iff t ht f).mpr hf
  change t • g = f at hg
  rw [← hg]
  change (1 : A) ⊗ₜ[R] (t • g) = 0
  rw [← TensorProduct.smul_tmul]
  have heq : t • (1 : A) = 0 := by
    simp only [Algebra.smul_def, mul_one]
    have hmem : t ∈ RingHom.ker (algebraMap R A) := by
      rw [hker]
      exact Ideal.subset_span (Set.mem_singleton t)
    exact hmem
  rw [heq, TensorProduct.zero_tmul]
end DualCartierRestriction

end


/-! Finite presentation of the associated sheaf of a finite module over a Noetherian ring. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry

namespace CoherentAffine
variable {R : CommRingCat} (M : ModuleCat R)

lemma isFinitePresentation_tilde [Module.FinitePresentation R M] :
    SheafOfModules.IsFinitePresentation (tilde M) := by
  obtain ⟨s, hs, hker⟩ := Module.FinitePresentation.out (R := R) (M := M)
  obtain ⟨t, ht⟩ := hker
  let P := presentationTilde M (s : Set M) hs (t : Set ((s : Set M) →₀ R)) ht
  have hgen : Finite P.generators.I := by
    change Finite (s : Set M)
    infer_instance
  have hrel : Finite P.relations.I := by
    change Finite (t : Set ((s : Set M) →₀ R))
    infer_instance
  have : P.IsFinite := ⟨⟨hgen⟩, ⟨hrel⟩⟩
  refine ⟨⟨P.quasicoherentData, ?_⟩⟩
  constructor
  intro U
  constructor
  · constructor
    change Finite P.generators.I
    exact hgen
  · constructor
    change Finite P.relations.I
    exact hrel

lemma coherent_tilde [IsNoetherianRing R] [Module.Finite R M] :
    SheafOfModules.IsFinitePresentation (tilde M) := by
  have := Module.finitePresentation_of_finite R M
  exact isFinitePresentation_tilde M

end CoherentAffine

end

noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace CoherentGlobal
open Scheme.Modules
/-- Restriction along a quotient is fully faithful on modules. -/
def restrictScalarsFullyFaithful {A B : Type} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Surjective f) :
    (ModuleCat.restrictScalars f).FullyFaithful where
  preimage {M N} g := ModuleCat.ofHom
    { g.hom.toAddHom with
      map_smul' := by
        intro b m
        obtain ⟨a, rfl⟩ := hf b
        exact g.hom.map_smul a m }
  map_preimage _ := rfl
  preimage_map _ := rfl

lemma affineGamma_injective {R : CommRingCat.{0}} (M N : (Spec R).Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent] :
    Function.Injective (fun g : M ⟶ N => (moduleSpecΓFunctor (R := R)).map g) := by
  intro f g h
  let M' : (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).FullSubcategory :=
    ⟨M, inferInstance⟩
  let N' : (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).FullSubcategory :=
    ⟨N, inferInstance⟩
  have h' : (tildeEquiv (R := R)).inverse.map
      (ObjectProperty.homMk (X := M') (Y := N') f) =
      (tildeEquiv (R := R)).inverse.map (ObjectProperty.homMk g) := h
  exact congrArg (fun z : M' ⟶ N' => z.hom)
    ((tildeEquiv (R := R)).inverse.map_injective h')

lemma affineGamma_surjective {R : CommRingCat.{0}} (M N : (Spec R).Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent] :
    Function.Surjective (fun g : M ⟶ N => (moduleSpecΓFunctor (R := R)).map g) := by
  intro g
  let M' : (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).FullSubcategory :=
    ⟨M, inferInstance⟩
  let N' : (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).FullSubcategory :=
    ⟨N, inferInstance⟩
  obtain ⟨p, hp⟩ := (tildeEquiv (R := R)).inverse.map_surjective
    (X := M') (Y := N') g
  exact ⟨p.hom, hp⟩

lemma quasicoherent_pushforward_affine {A B : CommRingCat.{0}} (f : A ⟶ B)
    (M : (Spec B).Modules) [M.IsQuasicoherent] :
    ((pushforward (Spec.map f)).obj M).IsQuasicoherent := by
  apply (isQuasicoherent_iff_isIso_fromTildeΓ _).mpr
  exact isIso_fromTildeΓ_pushforward f M

/-- The sheaf pushforward under an affine closed immersion is full on quasicoherent sheaves, by the
affine comparison. -/
lemma affinePushforward_full {A B : CommRingCat.{0}} (f : A ⟶ B)
    (hf : Function.Surjective f.hom) (M N : (Spec B).Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent] :
    Function.Surjective (fun g : M ⟶ N => (pushforward (Spec.map f)).map g) := by
  intro g
  let e := AffinePullback.pushforwardGammaIso f
  let p := (e.app M).inv ≫ (moduleSpecΓFunctor (R := A)).map g ≫ (e.app N).hom
  let h := (restrictScalarsFullyFaithful f.hom hf).preimage p
  have hh : (ModuleCat.restrictScalars f.hom).map h = p :=
    (restrictScalarsFullyFaithful f.hom hf).map_preimage p
  obtain ⟨u, hu⟩ := affineGamma_surjective M N h
  refine ⟨u, ?_⟩
  have := quasicoherent_pushforward_affine f M
  have := quasicoherent_pushforward_affine f N
  apply affineGamma_injective
  apply (cancel_mono (e.app N).hom).mp
  have hn := e.hom.naturality u
  change (moduleSpecΓFunctor (R := A)).map ((pushforward (Spec.map f)).map u) ≫
      (e.app N).hom = (e.app M).hom ≫
      (ModuleCat.restrictScalars f.hom).map ((moduleSpecΓFunctor (R := B)).map u) at hn
  change (moduleSpecΓFunctor (R := B)).map u = h at hu
  change (moduleSpecΓFunctor (R := A)).map ((pushforward (Spec.map f)).map u) ≫
    (e.app N).hom = (moduleSpecΓFunctor (R := A)).map g ≫ (e.app N).hom
  rw [hn, hu, hh]
  simp [p]
end CoherentGlobal

end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace CoherentGlobal
open Scheme.Modules
variable (R : CommRingCat.{0}) [IsNoetherianRing R]

/-- The associated sheaf functor on finite modules. -/
def cohTilde : FGModuleCat.{0} R ⥤ Coh (Spec R) :=
  (SheafOfModules.isFinitePresentation (Spec R).ringCatSheaf).lift
    (forget₂ (FGModuleCat.{0} R) (ModuleCat.{0} R) ⋙ tilde.functor R)
    (fun M => CoherentAffine.coherent_tilde M.obj)

/-- Sections of a coherent sheaf on an affine Noetherian scheme form a finite module. -/
def cohGamma : Coh (Spec R) ⥤ FGModuleCat.{0} R :=
  (ModuleCat.isFG R).lift
    (cohInclusion (Spec R) ⋙ moduleSpecΓFunctor (R := R)) (fun M => by
      let := M.property
      exact finiteGamma_of_coherent M.obj)

instance cohTilde_faithful : (cohTilde R).Faithful where
  map_injective {M N} f g h := by
    apply ObjectProperty.hom_ext
    apply (tilde.functor R).map_injective
    exact congrArg (fun f => f.hom) h

instance cohTilde_full : (cohTilde R).Full where
  map_surjective {M N} f := by
    refine ⟨ObjectProperty.homMk ((tilde.functor R).preimage f.hom), ?_⟩
    apply ObjectProperty.hom_ext
    exact (tilde.functor R).map_preimage f.hom

instance cohTilde_essSurj : (cohTilde R).EssSurj where
  mem_essImage M := by
    have : M.obj.IsFinitePresentation := M.property
    have : M.obj.IsQuasicoherent := inferInstance
    have : IsIso (Scheme.Modules.fromTildeΓ M.obj) :=
      (isQuasicoherent_iff_isIso_fromTildeΓ M.obj).mp inferInstance
    let e := asIso (Scheme.Modules.fromTildeΓ M.obj)
    refine ⟨(cohGamma R).obj M, ?_⟩
    exact ⟨ObjectProperty.isoMk _ e⟩

instance cohTilde_equivalence : (cohTilde R).IsEquivalence where

/-- Affine coherent sheaves are genuinely equivalent to finite modules. -/
def affineCohEquiv : FGModuleCat.{0} R ≌ Coh (Spec R) := (cohTilde R).asEquivalence

instance cohTilde_additive : (cohTilde R).Additive where
  map_add := by
    intros
    apply ObjectProperty.hom_ext
    exact (tilde.functor R).map_add

end CoherentGlobal

end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace CoherentDual
open Scheme.Modules
variable {A B : CommRingCat.{0}} [IsNoetherianRing A] [IsNoetherianRing B]
  (φ : A ⟶ B) (M : ModuleCat A) [Module.Finite A M]

abbrev algebraSpecMap : Spec B ⟶ Spec A := Spec.map φ

instance algebraTensor_finite :
    Module.Finite B ((ModuleCat.extendScalars φ.hom).obj M) := by
  let : Algebra A B := φ.hom.toAlgebra
  change Module.Finite B (TensorProduct A B M)
  infer_instance

/-- Canonical specialization into the dual over the target of a ring map. -/
def algebraDualInjection :
    (Scheme.Modules.pullback (algebraSpecMap φ)).obj
      (homSheaf (Spec A).sheaf (tilde M) (SheafOfModules.unit _)) ⟶
    homSheaf (Spec B).sheaf
      (tilde ((ModuleCat.extendScalars φ.hom).obj M))
      (SheafOfModules.unit _) := by
  letI : Algebra A B := φ.hom.toAlgebra
  exact (Scheme.Modules.pullback (algebraSpecMap φ)).map (affineDualIso M).inv ≫
    ((AffinePullback.pullbackTildeIso φ).app
      (ModuleCat.of A (Module.Dual A M))).hom ≫
    (tilde.functor B).map
      (dualBaseChangeMorphism φ M) ≫
    (affineDualIso ((ModuleCat.extendScalars φ.hom).obj M)).hom

lemma algebraDualInjection_mono
    (h : Function.Surjective φ.hom) (t : A) (ht : IsSMulRegular A t)
    (hker : RingHom.ker φ.hom = Ideal.span ({t} : Set A)) :
    Mono (algebraDualInjection φ M) := by
  let : Algebra A B := φ.hom.toAlgebra
  have : Mono (dualBaseChangeMorphism φ M) :=
    (ModuleCat.mono_iff_injective _).mpr
      (DualCartierRestriction.dualBaseChangeMap_injective_of_surjective h t ht hker)
  let a := (Scheme.Modules.pullback (algebraSpecMap φ)).map (affineDualIso M).inv
  let b := ((AffinePullback.pullbackTildeIso φ).app
    (ModuleCat.of A (Module.Dual A M))).hom
  let c := (tilde.functor B).map
    (dualBaseChangeMorphism φ M)
  let d := (affineDualIso ((ModuleCat.extendScalars φ.hom).obj M)).hom
  have : IsIso a := ((Scheme.Modules.pullback _).mapIso (affineDualIso M).symm).isIso_hom
  have : IsIso b := ((AffinePullback.pullbackTildeIso _).app
    (ModuleCat.of A (Module.Dual A M))).isIso_hom
  have : Mono c := (CoherentExactAffine.preservesMonomorphisms (R := B)).preserves _
  have : IsIso d := (affineDualIso _).isIso_hom
  change Mono (a ≫ b ≫ c ≫ d)
  exact mono_comp' (IsIso.mono_of_iso a) (mono_comp' (IsIso.mono_of_iso b) (mono_comp' ‹Mono c› (IsIso.mono_of_iso d)))

lemma tildeDual_algebra_restriction_torsionFree [IsDomain B]
    (h : Function.Surjective φ.hom) (t : A) (ht : IsSMulRegular A t)
    (hker : RingHom.ker φ.hom = Ideal.span ({t} : Set A))
    (U : (Spec B).Opensᵒᵖ) :
    @Module.IsTorsionFree ((Spec B).sheaf.obj.obj U)
      (((Scheme.Modules.pullback (algebraSpecMap φ)).obj
        (homSheaf (Spec A).sheaf (tilde M) (SheafOfModules.unit _))).val.obj U) _ _
      ((((Scheme.Modules.pullback (algebraSpecMap φ)).obj
        (homSheaf (Spec A).sheaf (tilde M) (SheafOfModules.unit _))).val.obj U).isModule) := by
  have : Mono (algebraDualInjection φ M) := algebraDualInjection_mono φ M h t ht hker
  exact SheafTorsion.subobject (algebraDualInjection φ M)
    (fun V => dual_sections_torsionFree _ V.unop) U

/-- Specialization of a coherent sheaf dual to an integral Cartier quotient is torsion-free, using
its finite module of sections. -/
lemma affineDual_algebra_restriction_torsionFree [IsDomain B]
    (N : (Spec A).Modules) [N.IsFinitePresentation]
    (h : Function.Surjective φ.hom) (t : A) (ht : IsSMulRegular A t)
    (hker : RingHom.ker φ.hom = Ideal.span ({t} : Set A))
    (U : (Spec B).Opensᵒᵖ) :
    @Module.IsTorsionFree ((Spec B).sheaf.obj.obj U)
      (((Scheme.Modules.pullback (algebraSpecMap φ)).obj
        (homSheaf (Spec A).sheaf N (SheafOfModules.unit _))).val.obj U) _ _
      ((((Scheme.Modules.pullback (algebraSpecMap φ)).obj
        (homSheaf (Spec A).sheaf N (SheafOfModules.unit _))).val.obj U).isModule) := by
  let M := moduleSpecΓFunctor.obj N
  have : Module.Finite A M := CoherentGlobal.finiteGamma_of_coherent N
  have : N.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData N).choose.isQuasicoherent
  have : IsIso (Scheme.Modules.fromTildeΓ N) := isIso_fromTildeΓ_of_isQuasicoherent N
  let e := (Scheme.Modules.pullback (algebraSpecMap φ)).mapIso
    ((homSheafFunctor (Spec A).sheaf (SheafOfModules.unit _)).mapIso
      (asIso (Scheme.Modules.fromTildeΓ N)).op)
  exact SheafTorsion.subobject e.hom
    (fun V => tildeDual_algebra_restriction_torsionFree φ M h t ht hker V) U
end CoherentDual

end

noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry TopologicalSpace
namespace CoherentGlobal
open Scheme.Modules

/-- The largest target open whose inverse image lies in a given source open. -/
def closedLiftOpen {X Y : Scheme.{0}} (f : X ⟶ Y) [IsClosedImmersion f]
    (U : X.Opens) : Y.Opens :=
  ⟨(f '' (U : Set X)ᶜ)ᶜ, (f.isClosedEmbedding.isClosedMap _ U.isOpen.isClosed_compl).isOpen_compl⟩

lemma preimage_closedLiftOpen {X Y : Scheme.{0}} (f : X ⟶ Y) [IsClosedImmersion f]
    (U : X.Opens) : f ⁻¹ᵁ closedLiftOpen f U = U := by
  ext x
  change (f x ∉ f '' (U : Set X)ᶜ) ↔ x ∈ U
  constructor
  · intro h
    by_contra hn
    exact h ⟨x, hn, rfl⟩
  · rintro h ⟨y, hy, he⟩
    exact hy (f.isClosedEmbedding.injective he ▸ h)

lemma le_closedLiftOpen_iff {X Y : Scheme.{0}} (f : X ⟶ Y) [IsClosedImmersion f]
    (V : Y.Opens) (U : X.Opens) : V ≤ closedLiftOpen f U ↔ f ⁻¹ᵁ V ≤ U := by
  constructor
  · intro h x hx
    have hh := h hx
    change f x ∉ f '' (U : Set X)ᶜ at hh
    by_contra hn
    exact hh ⟨x, hn, rfl⟩
  · intro h y hy hh
    obtain ⟨x, hx, rfl⟩ := hh
    exact hx (h hy)

/-- The open-lift functor for a closed immersion. -/
def closedLiftFunctor {X Y : Scheme.{0}} (f : X ⟶ Y) [IsClosedImmersion f] :
    X.Opens ⥤ Y.Opens where
  obj := closedLiftOpen f
  map {U V} g := homOfLE ((le_closedLiftOpen_iff f _ _).mpr (by
    rw [preimage_closedLiftOpen]
    exact leOfHom g))

/-- Inverse image of opens is a reflective localization for a closed embedding. -/
def closedOpenAdjunction {X Y : Scheme.{0}} (f : X ⟶ Y) [IsClosedImmersion f] :
    Opens.map f.base ⊣ closedLiftFunctor f where
  unit := { app := fun U => homOfLE ((le_closedLiftOpen_iff f U _).mpr le_rfl) }
  counit := { app := fun U => eqToHom (preimage_closedLiftOpen f U) }

instance closedOpenCounitIso {X Y : Scheme.{0}} (f : X ⟶ Y) [IsClosedImmersion f] :
    IsIso (closedOpenAdjunction f).counit := by
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro U
  change IsIso (eqToHom (preimage_closedLiftOpen f U))
  infer_instance

/-- Additive presheaves are recovered fully faithfully from their direct images. -/
def closedPresheafFullyFaithful {X Y : Scheme.{0}} (f : X ⟶ Y) [IsClosedImmersion f] :
    ((Functor.whiskeringLeft Y.Opensᵒᵖ X.Opensᵒᵖ AddCommGrpCat).obj
      (Opens.map f.base).op).FullyFaithful := by
  let adj := (closedOpenAdjunction f).op.whiskerLeft (C := AddCommGrpCat)
  have : IsIso (closedOpenAdjunction f).op.unit := by
    change IsIso (NatTrans.op (closedOpenAdjunction f).counit)
    infer_instance
  have : IsIso adj.unit := by
    apply (NatTrans.isIso_iff_isIso_app _).mpr
    intro F
    change IsIso ((Functor.leftUnitor F).inv ≫
      Functor.whiskerRight (closedOpenAdjunction f).op.unit F ≫
      (Functor.associator _ _ _).hom)
    infer_instance
  exact adj.fullyFaithfulLOfIsIsoUnit
end CoherentGlobal

end

noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry TopologicalSpace
namespace CoherentGlobal
open Scheme.Modules

instance closedPushforward_faithful {X Y : Scheme.{0}} (f : X ⟶ Y) [IsClosedImmersion f] :
    (show X.Modules ⥤ Y.Modules from pushforward f).Faithful where
  map_injective {M N} u v h := by
    apply (toPresheaf X).map_injective
    apply (closedPresheafFullyFaithful f).map_injective
    exact congrArg (fun z : (pushforward f).obj M ⟶ (pushforward f).obj N =>
      z.mapPresheaf) h

/-- Underlying additive natural transformation of the descended map. -/
def closedPushforwardPreimageAdd {X Y : Scheme.{0}} (f : X ⟶ Y) [IsClosedImmersion f]
    {M N : X.Modules} (g : (pushforward f).obj M ⟶ (pushforward f).obj N) :
    M.presheaf ⟶ N.presheaf :=
  (closedPresheafFullyFaithful f).preimage g.mapPresheaf

lemma closedPushforwardPreimageAdd_app {X Y : Scheme.{0}} (f : X ⟶ Y)
    [IsClosedImmersion f] {M N : X.Modules}
    (g : (pushforward f).obj M ⟶ (pushforward f).obj N) (V : Y.Opens) :
    (closedPushforwardPreimageAdd f g).app (op (f ⁻¹ᵁ V)) = g.app V := by
  exact NatTrans.congr_app ((closedPresheafFullyFaithful f).map_preimage
    (X := M.presheaf) (Y := N.presheaf) g.mapPresheaf) (op V)

lemma closedPushforward_add_linear {X Y : Scheme.{0}} (f : X ⟶ Y) [IsClosedImmersion f]
    {M N : X.Modules} (g : (pushforward f).obj M ⟶ (pushforward f).obj N)
    (h : M.presheaf ⟶ N.presheaf)
    (hh : ∀ V : Y.Opens, h.app (op (f ⁻¹ᵁ V)) = g.app V)
    (U : X.Opens) (r : Γ(X, U)) (m : Γ(M, U)) :
      h.app (op U) (r • m) = r • h.app (op U) m := by
    let I := {V : Y.affineOpens // V.1 ≤ closedLiftOpen f U}
    let V : I → X.Opens := fun V => f ⁻¹ᵁ V.1.1
    have hv (W : I) : V W ≤ U := (le_closedLiftOpen_iff f _ _).mp W.2
    have hcov : U ≤ ⨆ W : I, V W := by
      intro x hx
      have hfx : f x ∈ closedLiftOpen f U := by
        change x ∈ f ⁻¹ᵁ closedLiftOpen f U
        rwa [preimage_closedLiftOpen]
      obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset hfx
      exact Opens.mem_iSup.mpr ⟨⟨⟨W, hW⟩, hWU⟩, hxW⟩
    let Q : TopCat.Sheaf AddCommGrpCat X :=
      (SheafOfModules.toSheaf X.ringCatSheaf).obj N
    apply Q.eq_of_locally_eq' V U (fun W => homOfLE (hv W)) hcov
    intro W
    let i : V W ⟶ U := homOfLE (hv W)
    have hn (a : Γ(M, U)) :
        N.presheaf.map i.op (h.app (op U) a) =
          h.app (op (V W)) (M.presheaf.map i.op a) :=
      (CategoryTheory.congr_fun (h.naturality i.op) a).symm
    change N.presheaf.map i.op (h.app (op U) (r • m)) =
      N.presheaf.map i.op (r • h.app (op U) m)
    rw [hn, Scheme.Modules.map_smul, Scheme.Modules.map_smul, hn]
    change h.app (op (f ⁻¹ᵁ W.1.1))
        (X.presheaf.map i.op r • M.presheaf.map i.op m) =
      X.presheaf.map i.op r • h.app (op (f ⁻¹ᵁ W.1.1)) (M.presheaf.map i.op m)
    rw [hh]
    obtain ⟨s, hs⟩ := f.app_surjective W.1.1 W.1.2 (X.presheaf.map i.op r)
    rw [← hs]
    exact g.app_smul s (M.presheaf.map i.op m)

/-- Pushforward under a closed immersion is full on all structure-sheaf modules. The underlying
additive map is descended via the open adjunction; linearity is checked on inverse images of
affine opens, where the structure ring homomorphism is surjective. -/
lemma closedPushforward_full {X Y : Scheme.{0}} (f : X ⟶ Y) [IsClosedImmersion f]
    (M N : X.Modules) :
    Function.Surjective (fun u : M ⟶ N => (pushforward f).map u) := by
  intro g
  let h := closedPushforwardPreimageAdd f g
  have hlin := closedPushforward_add_linear f g h (closedPushforwardPreimageAdd_app f g)
  let u : M ⟶ N := ⟨PresheafOfModules.homMk h (fun U r m => hlin U.unop r m)⟩
  refine ⟨u, ?_⟩
  apply Scheme.Modules.hom_ext
  intro V
  exact closedPushforwardPreimageAdd_app f g V

instance closedPushforward_full_instance {X Y : Scheme.{0}} (f : X ⟶ Y)
    [IsClosedImmersion f] : (show X.Modules ⥤ Y.Modules from pushforward f).Full where
  map_surjective := closedPushforward_full f _ _
end CoherentGlobal

end

end OAI
