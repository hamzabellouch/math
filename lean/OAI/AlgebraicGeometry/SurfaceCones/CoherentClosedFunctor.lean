import OAI.AlgebraicGeometry.SurfaceCones.PushforwardRestrictionNatural

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace CoherentGlobal
open Scheme.Modules
instance cohClosedPushforward_full {X Y : Scheme.{0}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsClosedImmersion f] : (cohPushforward f).Full where
  map_surjective {M N} g := by
    obtain ⟨u, hu⟩ := closedPushforward_full f M.obj N.obj g.hom
    refine ⟨ObjectProperty.homMk u, ?_⟩
    apply ObjectProperty.hom_ext
    exact hu
instance cohClosedPushforward_faithful {X Y : Scheme.{0}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsClosedImmersion f] : (cohPushforward f).Faithful where
  map_injective {M N} u v h := by
    apply ObjectProperty.hom_ext
    apply (pushforward f).map_injective
    exact congrArg (fun z : (cohPushforward f).obj M ⟶ (cohPushforward f).obj N => z.hom) h
/-- Fully faithful exact closed pushforward on coherent sheaves. -/
def cohClosedPushforwardFullyFaithful {X Y : Scheme.{0}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsClosedImmersion f] : (cohPushforward f).FullyFaithful :=
  Functor.FullyFaithful.ofFullyFaithful _
end CoherentGlobal

end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace CoherentGlobal
open Scheme.Modules
variable {R : CommRingCat.{0}} [IsNoetherianRing R]

/-- A coherent affine sheaf annihilated by a principal ideal descends to a coherent sheaf on the
corresponding closed subscheme. -/
lemma exists_principal_descent (t : R) (M : (Spec R).Modules)
    [M.IsFinitePresentation]
    (h : Module.IsTorsionBy R (moduleSpecΓFunctor.obj M) t) :
    ∃ N : (Spec (CommRingCat.of (R ⧸ Ideal.span ({t} : Set R)))).Modules,
      N.IsFinitePresentation ∧ Nonempty
        ((pushforward (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (Ideal.span ({t} : Set R)))))).obj N ≅ M) := by
  have : M.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData M).choose.isQuasicoherent
  have hM : IsIso (fromTildeΓ M) := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  let Q := R ⧸ Ideal.span ({t} : Set R)
  let f : R ⟶ CommRingCat.of Q := CommRingCat.ofHom (Ideal.Quotient.mk _)
  let A : ModuleCat R := moduleSpecΓFunctor.obj M
  let : Module Q A := h.module
  let : IsScalarTower R Q A := by
    constructor
    intro r q a
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective q
    change (r * s) • a = r • s • a
    exact (smul_smul r s a).symm
  have : Module.Finite R A := finiteGamma_of_coherent M
  have : Module.Finite Q A := Module.Finite.of_restrictScalars_finite R Q A
  let B : ModuleCat (CommRingCat.of Q) := ModuleCat.of _ A
  let e : (ModuleCat.restrictScalars f.hom).obj B ≅ A :=
    (LinearEquiv.refl R A).toModuleIso
  refine ⟨tilde B, CoherentAffine.coherent_tilde B, ?_⟩
  exact ⟨AffinePullback.pushforwardTildeIso f B ≪≫
    (tilde.functor R).mapIso e ≪≫ @asIso _ _ _ _ (fromTildeΓ M) hM⟩

end CoherentGlobal

end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace CoherentGlobal
open Scheme.Modules
variable {R S : CommRingCat.{0}} [IsNoetherianRing R]

/-- Descent for a coherent module along an affine quotient. -/
lemma exists_quotient_descent (I : Ideal R) (M : (Spec R).Modules)
    [M.IsFinitePresentation]
    (h : Module.IsTorsionBySet R (moduleSpecΓFunctor.obj M) I) :
    ∃ N : (Spec (CommRingCat.of (R ⧸ I))).Modules,
      N.IsFinitePresentation ∧ Nonempty
        ((pushforward (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).obj N ≅ M) := by
  have : M.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData M).choose.isQuasicoherent
  have hM : IsIso (fromTildeΓ M) := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  let Q := R ⧸ I
  let f : R ⟶ CommRingCat.of Q := CommRingCat.ofHom (Ideal.Quotient.mk _)
  let A : ModuleCat R := moduleSpecΓFunctor.obj M
  let : Module Q A := h.module
  let : IsScalarTower R Q A := by
    constructor
    intro r q a
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective q
    change (r * s) • a = r • s • a
    exact (smul_smul r s a).symm
  have : Module.Finite R A := finiteGamma_of_coherent M
  have : Module.Finite Q A := Module.Finite.of_restrictScalars_finite R Q A
  let B : ModuleCat (CommRingCat.of Q) := ModuleCat.of _ A
  let e : (ModuleCat.restrictScalars f.hom).obj B ≅ A :=
    (LinearEquiv.refl R A).toModuleIso
  refine ⟨tilde B, CoherentAffine.coherent_tilde B, ?_⟩
  exact ⟨AffinePullback.pushforwardTildeIso f B ≪≫
    (tilde.functor R).mapIso e ≪≫ @asIso _ _ _ _ (fromTildeΓ M) hM⟩

/-- Descent along a surjective affine ring map, with annihilation of its kernel. The descended sheaf
is a finite-module associated sheaf. -/
lemma exists_surjective_descent (f : R ⟶ S) (hf : Function.Surjective f.hom)
    (M : (Spec R).Modules) [M.IsFinitePresentation]
    (h : Module.IsTorsionBySet R (moduleSpecΓFunctor.obj M) (RingHom.ker f.hom)) :
    ∃ N : (Spec S).Modules, N.IsFinitePresentation ∧
      Nonempty ((pushforward (Spec.map f)).obj N ≅ M) := by
  have : M.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData M).choose.isQuasicoherent
  have hM : IsIso (fromTildeΓ M) := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  let A : ModuleCat R := moduleSpecΓFunctor.obj M
  let Q := R ⧸ RingHom.ker f.hom
  let eqv : Q ≃+* S := f.hom.quotientKerEquivOfSurjective hf
  let : Module Q A := h.module
  let : Module S A := Module.compHom A eqv.symm.toRingHom
  let : Algebra R S := f.hom.toAlgebra
  have hsmul (r : R) (a : A) : f.hom r • a = r • a := by
    change eqv.symm (f.hom r) • a = r • a
    have hr : eqv.symm (f.hom r) = Ideal.Quotient.mk (RingHom.ker f.hom) r :=
      eqv.symm_apply_eq.mpr rfl
    rw [hr]
    rfl
  let : IsScalarTower R S A := by
    constructor
    intro r s a
    change (f.hom r * s) • a = r • s • a
    rw [mul_smul, hsmul]
  have : Module.Finite R A := finiteGamma_of_coherent M
  have : Module.Finite S A := Module.Finite.of_restrictScalars_finite R S A
  have : IsNoetherianRing S := isNoetherianRing_of_surjective R S f.hom hf
  let B : ModuleCat S := ModuleCat.of _ A
  let e : (ModuleCat.restrictScalars f.hom).obj B ≅ A :=
    (show (ModuleCat.restrictScalars f.hom).obj B ≃ₗ[R] A from
      { Equiv.refl A with
        map_add' := fun _ _ => rfl
        map_smul' := fun r a => hsmul r a }).toModuleIso
  refine ⟨tilde B, CoherentAffine.coherent_tilde B, ?_⟩
  exact ⟨AffinePullback.pushforwardTildeIso f B ≪≫
    (tilde.functor R).mapIso e ≪≫ @asIso _ _ _ _ (fromTildeΓ M) hM⟩
end CoherentGlobal

end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace CoherentGlobal
open Scheme.Modules

/-- Pushforward around a scheme isomorphism. -/
def pushforwardIsoRoundtrip {X Y : Scheme.{0}} (e : X ≅ Y) :
    pushforward e.hom ⋙ pushforward e.inv ≅ 𝟭 X.Modules :=
  pushforwardComp e.hom e.inv ≪≫ pushforwardCongr e.hom_inv_id ≪≫ pushforwardId X

/-- Closed-support descent on affine schemes, without requiring them to be definitionally spectra.
The hypothesis is annihilation by the kernel on the canonical affine chart of the target. -/
lemma exists_affine_closed_preimage {X Y : Scheme.{0}} [IsAffine Y]
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [IsClosedImmersion f]
    (M : Y.Modules) [M.IsFinitePresentation]
    (h : Module.IsTorsionBySet Γ(Y, ⊤)
      (moduleSpecΓFunctor.obj ((pushforward Y.isoSpec.hom).obj M))
      (RingHom.ker f.appTop.hom)) :
    ∃ N : X.Modules, N.IsFinitePresentation ∧ Nonempty ((pushforward f).obj N ≅ M) := by
  have hf := IsClosedImmersion.isAffine_surjective_of_isAffine f
  have : IsAffine X := hf.1
  have : IsNoetherianRing Γ(Y, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top Y⟩
  have : ((pushforward Y.isoSpec.hom).obj M).IsFinitePresentation :=
    coherent_pushforward_iso Y.isoSpec M
  obtain ⟨N, hN, ⟨e⟩⟩ := exists_surjective_descent f.appTop hf.2
    ((pushforward Y.isoSpec.hom).obj M) h
  let := hN
  refine ⟨(pushforward X.isoSpec.inv).obj N,
    coherent_pushforward_iso X.isoSpec.symm N, ?_⟩
  refine ⟨(pushforwardComp X.isoSpec.inv f).app N ≪≫
    (pushforwardCongr (Scheme.isoSpec_inv_naturality f).symm).app N ≪≫
    (pushforwardComp (Spec.map f.appTop) Y.isoSpec.inv).symm.app N ≪≫
    (pushforward Y.isoSpec.inv).mapIso e ≪≫ (pushforwardIsoRoundtrip Y.isoSpec).app M⟩
end CoherentGlobal

end

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace BeckChevalleyUnit
universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]
  {F₁ : A ⥤ C} {U₁ : C ⥤ A} {F₂ : B ⥤ D} {U₂ : D ⥤ B}
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
  (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : F₁ ⊣ U₁) (a₄ : F₂ ⊣ U₂)

/-- The other mate of a square is invertible when its twice-adjoint comparison is invertible. -/
lemma isIso_other_mate (s : TwoSquare R₁ F₂ F₁ R₂)
    [IsIso ((mateEquiv a₄ a₃ s).natTrans)] :
    IsIso (((mateEquiv a₁ a₂).symm s).natTrans) := by
  let b := (mateEquiv a₁ a₂).symm s
  have he : (mateEquiv a₄ a₃ s).natTrans =
      conjugateEquiv (a₁.comp a₄) (a₃.comp a₂) b.natTrans := by
    simpa only [b, Equiv.apply_symm_apply] using
      iterated_mateEquiv_conjugateEquiv a₁ a₂ a₃ a₄ b
  have : IsIso (conjugateEquiv (a₁.comp a₄) (a₃.comp a₂) b.natTrans) :=
    he ▸ inferInstance
  exact conjugateEquiv_of_iso (a₁.comp a₄) (a₃.comp a₂) b.natTrans

/-- Under an invertible base-change square and its invertible mate, the restricted original unit is
invertible at every object at which the local unit is invertible. This is the local descent step
for closed support. -/
lemma map_unit_isIso (s : TwoSquare R₁ F₂ F₁ R₂)
    [IsIso s.natTrans] [IsIso (((mateEquiv a₁ a₂).symm s).natTrans)]
    (M : A) [IsIso (a₂.unit.app (F₁.obj M))] : IsIso (F₁.map (a₁.unit.app M)) := by
  have he := unit_mateEquiv_symm a₁ a₂ s M
  have : IsIso (F₁.map (a₁.unit.app M) ≫ s.app (L₁.obj M)) := by
    rw [he]
    change IsIso (a₂.unit.app (F₁.obj M) ≫
      R₂.map (((mateEquiv a₁ a₂).symm s).natTrans.app M))
    infer_instance
  have : IsIso (s.app (L₁.obj M)) :=
    (inferInstance : IsIso (s.natTrans.app (L₁.obj M)))
  exact (IsIso.of_isIso_comp_right (F₁.map (a₁.unit.app M)) (s.app (L₁.obj M)))
end BeckChevalleyUnit

end

noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace CoherentBaseChange
open Scheme.Modules
variable {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens)

/-- Open pushforward comparison viewed as a square of functors. -/
def restrictSquare : TwoSquare (pushforward f) (restrictFunctor (f ⁻¹ᵁ U).ι)
    (restrictFunctor U.ι) (pushforward (f ∣_ U)) :=
  .mk _ _ _ _ (pushforwardRestrictNatIso f U).hom

/-- The twice-right-adjoint comparison of the open base-change square. -/
def rightSquare := mateEquiv (restrictAdjunction (f ⁻¹ᵁ U).ι)
  (restrictAdjunction U.ι) (restrictSquare f U)

/-- Commutativity of the square gives an isomorphism of composite pushforwards, without base-change
assumptions about quasicoherent sheaves. -/
def rightSquareIso : pushforward (f ⁻¹ᵁ U).ι ⋙ pushforward f ≅
    pushforward (f ∣_ U) ⋙ pushforward U.ι :=
  pushforwardComp (f ⁻¹ᵁ U).ι f ≪≫
    pushforwardCongr (morphismRestrict_ι f U).symm ≪≫
    (pushforwardComp (f ∣_ U) U.ι).symm

lemma pushforwardRestrictNatIso_hom_app_app (M : X.Modules) (V : U.toScheme.Opens) :
    ((pushforwardRestrictNatIso f U).hom.app M).app V =
      M.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V)).op := rfl

lemma rightSquare_eq : (rightSquare f U).natTrans = (rightSquareIso f U).hom := by
  apply NatTrans.ext
  funext M
  apply Scheme.Modules.hom_ext
  intro V
  simp only [rightSquare, mateEquiv, Equiv.coe_fn_mk, restrictSquare,
    NatTrans.comp_app, Functor.rightUnitor_inv_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.whiskerRight_app, Functor.comp_map, Functor.leftUnitor_hom_app,
    Functor.comp_obj, Category.id_comp]
  dsimp only [TwoSquare.mk, TwoSquare.natTrans]
  simp only [Scheme.Modules.Hom.comp_app, pushforward_map_app, restrictAdjunction_unit_app_app,
    restrictAdjunction_counit_app_app]
  simp only [pushforward_obj_presheaf_map, pushforwardRestrictNatIso_hom_app_app,
    rightSquareIso, Iso.trans_hom, NatTrans.comp_app,
    Scheme.Modules.Hom.comp_app, pushforwardComp_hom_app_app,
    pushforwardCongr_hom_app_app]
  change M.presheaf.map _ ≫ M.presheaf.map _ ≫ M.presheaf.map _ ≫ 𝟙 _ =
    𝟙 _ ≫ M.presheaf.map _ ≫ 𝟙 _
  simp only [Category.id_comp, Category.comp_id]
  rw [← M.presheaf.map_comp, ← M.presheaf.map_comp]
  congr 1

instance rightSquare_natTrans_isIso : IsIso (rightSquare f U).natTrans := by
  rw [rightSquare_eq]
  infer_instance

instance pullbackSquare_natTrans_isIso : IsIso
    (((mateEquiv (pullbackPushforwardAdjunction f)
      (pullbackPushforwardAdjunction (f ∣_ U))).symm (restrictSquare f U)).natTrans) := by
  have : IsIso ((mateEquiv (restrictAdjunction (f ⁻¹ᵁ U).ι)
      (restrictAdjunction U.ι) (restrictSquare f U)).natTrans) :=
    rightSquare_natTrans_isIso f U
  exact BeckChevalleyUnit.isIso_other_mate
    (pullbackPushforwardAdjunction f) (pullbackPushforwardAdjunction (f ∣_ U))
    (restrictAdjunction U.ι) (restrictAdjunction (f ⁻¹ᵁ U).ι) (restrictSquare f U)

/-- Pullback commutes with open restriction through the canonical mate, compatibly with the
pullback-pushforward unit. -/
def pullbackRestrictNatIso : restrictFunctor U.ι ⋙ pullback (f ∣_ U) ≅
    pullback f ⋙ restrictFunctor (f ⁻¹ᵁ U).ι :=
  asIso (((mateEquiv (pullbackPushforwardAdjunction f)
    (pullbackPushforwardAdjunction (f ∣_ U))).symm (restrictSquare f U)).natTrans)

/-- The restricted global unit is invertible whenever its local counterpart is. -/
lemma restrict_unit_isIso (M : Y.Modules)
    [IsIso ((pullbackPushforwardAdjunction (f ∣_ U)).unit.app
      ((restrictFunctor U.ι).obj M))] :
    IsIso ((restrictFunctor U.ι).map ((pullbackPushforwardAdjunction f).unit.app M)) := by
  have : IsIso (restrictSquare f U).natTrans :=
    (inferInstance : IsIso (pushforwardRestrictNatIso f U).hom)
  exact BeckChevalleyUnit.map_unit_isIso (pullbackPushforwardAdjunction f)
    (pullbackPushforwardAdjunction (f ∣_ U)) (restrictSquare f U) M

end CoherentBaseChange

end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace CoherentGlobal
open Scheme.Modules
/-- A morphism of scheme-module sheaves is invertible when its restrictions to all affine opens are
invertible. -/
lemma isIso_of_affine_restrict {X : Scheme.{0}} {M N : X.Modules} (f : M ⟶ N)
    (h : ∀ U : X.affineOpens, IsIso ((restrictFunctor U.1.ι).map f)) : IsIso f := by
  have hk : IsZero (kernel f) := by
    apply isZero_of_affine_restrict
    intro U
    let := h U
    have : PreservesFiniteLimits (restrictFunctor U.1.ι) :=
      CoherentRestriction.preservesFiniteLimits U.1.ι
    exact (isZero_kernel_of_mono ((restrictFunctor U.1.ι).map f)).of_iso
      (PreservesKernel.iso (restrictFunctor U.1.ι) f)
  have hc : IsZero (cokernel f) := by
    apply isZero_of_affine_restrict
    intro U
    let := h U
    exact (isZero_cokernel_of_epi ((restrictFunctor U.1.ι).map f)).of_iso
      (PreservesCokernel.iso (restrictFunctor U.1.ι) f)
  have : Mono f := Abelian.mono_of_kernel_ι_eq_zero f (hk.eq_of_src _ _)
  have : Epi f := Abelian.epi_of_cokernel_π_eq_zero f (hc.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi f
end CoherentGlobal

end

noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafLocality
universe u
variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  {A : Type*} [Category* A] {ι : Type*} {X : ι → C}

/-- Equality of sheaf morphisms can be checked on any covering family. -/
lemma hom_ext_of_coversTop (hX : J.CoversTop X)
    {F G : Sheaf J A} {f g : F ⟶ G}
    (h : ∀ i, (J.overPullback A (X i)).map f = (J.overPullback A (X i)).map g) :
    f = g := by
  apply Sheaf.hom_ext
  ext W
  have heq (Z : C) (i : ι) (a : Z ⟶ X i) :
      f.hom.app (op Z) = g.hom.app (op Z) := by
    exact NatTrans.congr_app (congrArg (fun q => q.hom) (h i)) (op (Over.mk a))
  let S : J.Cover W.unop := hX.cover W.unop
  apply G.property.hom_ext S
  intro I
  obtain ⟨i, ⟨a⟩⟩ := I.hf
  rw [← f.hom.naturality, ← g.hom.naturality, heq I.Y i a]

/-- Monomorphism is local on a cover. No stalk-exactness assumption is used. -/
lemma mono_of_coversTop (hX : J.CoversTop X)
    {F G : Sheaf J A} (f : F ⟶ G)
    (h : ∀ i, Mono ((J.overPullback A (X i)).map f)) : Mono f := by
  constructor
  intro H a b hab
  apply hom_ext_of_coversTop hX
  intro i
  have := h i
  apply (cancel_mono ((J.overPullback A (X i)).map f)).mp
  simpa only [Functor.map_comp] using congrArg ((J.overPullback A (X i)).map) hab

/-- The same descent statement for module sheaves. -/
lemma module_mono_of_coversTop (R : Sheaf J RingCat.{u}) (hX : J.CoversTop X)
    {F G : SheafOfModules.{u} R} (f : F ⟶ G)
    (h : ∀ i, Mono ((SheafOfModules.overFunctor R (X i)).map f)) : Mono f := by
  have : Mono ((SheafOfModules.toSheaf R).map f) := by
    apply mono_of_coversTop hX
    intro i
    have := h i
    exact (inferInstance : Mono ((SheafOfModules.toSheaf (R.over (X i))).map
      ((SheafOfModules.overFunctor R (X i)).map f)))
  exact (Functor.mono_of_mono_map (SheafOfModules.toSheaf R) inferInstance)
end SheafLocality

end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry TopologicalSpace
namespace CoherentGlobal
open Scheme.Modules
variable {X : Scheme.{0}} {I : Type} (U : I → X.Opens) (hU : iSup U = ⊤)

include hU

/-- Equality of scheme-module morphisms descends along an arbitrary open cover; affine charts are
not required. -/
lemma hom_ext_of_open_cover {M N : X.Modules} {f g : M ⟶ N}
    (h : ∀ i, (restrictFunctor (U i).ι).map f = (restrictFunctor (U i).ι).map g) :
    f = g := by
  have ho (i : I) : (SheafOfModules.overFunctor X.ringCatSheaf (U i)).map f =
      (SheafOfModules.overFunctor X.ringCatSheaf (U i)).map g := by
    apply (overEquiv (U i)).functor.map_injective
    have : IsIso ((overFunctorEquiv (U i)).hom.app N) :=
      ((overFunctorEquiv (U i)).app N).isIso_hom
    apply (cancel_mono ((overFunctorEquiv (U i)).hom.app N)).mp
    change ((SheafOfModules.overFunctor X.ringCatSheaf (U i) ⋙
      (overEquiv (U i)).functor).map f) ≫ _ = _
    calc
      _ = (overFunctorEquiv (U i)).hom.app M ≫ (restrictFunctor (U i).ι).map f :=
        (overFunctorEquiv (U i)).hom.naturality f
      _ = (overFunctorEquiv (U i)).hom.app M ≫ (restrictFunctor (U i).ι).map g := by
        rw [h i]
      _ = _ := ((overFunctorEquiv (U i)).hom.naturality g).symm
  apply (SheafOfModules.toSheaf X.ringCatSheaf).map_injective
  apply SheafLocality.hom_ext_of_coversTop ((Opens.coversTop_iff X U).mpr hU)
  intro i
  exact congrArg ((SheafOfModules.toSheaf (X.ringCatSheaf.over (U i))).map) (ho i)

lemma isZero_of_open_cover (M : X.Modules)
    (h : ∀ i, IsZero ((restrictFunctor (U i).ι).obj M)) : IsZero M := by
  apply (IsZero.iff_id_eq_zero M).mpr
  apply hom_ext_of_open_cover U hU
  intro i
  exact (h i).eq_of_src _ _

/-- Isomorphism of module sheaves is local on an open cover. -/
lemma isIso_of_open_cover {M N : X.Modules} (f : M ⟶ N)
    (h : ∀ i, IsIso ((restrictFunctor (U i).ι).map f)) : IsIso f := by
  have hk : IsZero (kernel f) := by
    apply isZero_of_open_cover U hU
    intro i
    let := h i
    have : PreservesFiniteLimits (restrictFunctor (U i).ι) :=
      CoherentRestriction.preservesFiniteLimits (U i).ι
    exact (isZero_kernel_of_mono ((restrictFunctor (U i).ι).map f)).of_iso
      (PreservesKernel.iso (restrictFunctor (U i).ι) f)
  have hc : IsZero (cokernel f) := by
    apply isZero_of_open_cover U hU
    intro i
    let := h i
    exact (isZero_cokernel_of_epi ((restrictFunctor (U i).ι).map f)).of_iso
      (PreservesCokernel.iso (restrictFunctor (U i).ι) f)
  have : Mono f := Abelian.mono_of_kernel_ι_eq_zero f (hk.eq_of_src _ _)
  have : Epi f := Abelian.epi_of_cokernel_π_eq_zero f (hc.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi f

lemma coherent_of_open_cover (M : X.Modules)
    (h : ∀ i, ((restrictFunctor (U i).ι).obj M).IsFinitePresentation) :
    M.IsFinitePresentation := by
  have (i : I) : (M.over (U i)).IsFinitePresentation := by
    let := h i
    exact coherent_over_of_restrict (U i) M
  exact CoherentLocality.finitePresentation_of_coversTop M U
    ((Opens.coversTop_iff X U).mpr hU)
end CoherentGlobal

end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry TopologicalSpace
namespace CoherentGlobal
open Scheme.Modules
variable {X Y : Scheme.{0}} (f : X ⟶ Y) [IsClosedImmersion f]
variable {I : Type} (U : I → Y.Opens) (hU : iSup U = ⊤)
variable (M : Y.Modules) (N : ∀ i, (f ⁻¹ᵁ U i).toScheme.Modules)
  (e : ∀ i, (pushforward (f ∣_ U i)).obj (N i) ≅ (restrictFunctor (U i).ι).obj M)

include hU e in
/-- Membership in the essential image of closed pushforward is local on an open cover, with descent
given by pullback. -/
lemma closedDescent_unit_isIso : IsIso ((pullbackPushforwardAdjunction f).unit.app M) := by
  apply isIso_of_open_cover U hU
  intro i
  have : IsIso ((pullbackPushforwardAdjunction (f ∣_ U i)).unit.app
      ((restrictFunctor (U i).ι).obj M)) :=
    (pullbackPushforwardAdjunction (f ∣_ U i)).isIso_unit_app_of_iso (e i).symm
  exact CoherentBaseChange.restrict_unit_isIso f (U i) M

/-- Canonical local comparison of the descended module with its given closed-support representative. -/
def closedDescent_localIso (i : I) :
    (restrictFunctor (f ⁻¹ᵁ U i).ι).obj ((Scheme.Modules.pullback f).obj M) ≅ N i :=
  ((CoherentBaseChange.pullbackRestrictNatIso f (U i)).app M).symm ≪≫
    (Scheme.Modules.pullback (f ∣_ U i)).mapIso (e i).symm ≪≫
    asIso ((pullbackPushforwardAdjunction (f ∣_ U i)).counit.app (N i))

omit [IsClosedImmersion f] in
include hU in
lemma preimage_cover : (⨆ i, f ⁻¹ᵁ U i) = ⊤ := by
  apply top_unique
  intro x _
  have hx : f x ∈ (⨆ i, U i) := by rw [hU]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  exact Opens.mem_iSup.mpr ⟨i, hi⟩

include hU e in
/-- Pullback is coherent for objects which locally are coherent sheaves with closed support. -/
lemma closedDescent_coherent (hN : ∀ i, (N i).IsFinitePresentation) :
    ((Scheme.Modules.pullback f).obj M).IsFinitePresentation := by
  apply coherent_of_open_cover (fun i => f ⁻¹ᵁ U i) (preimage_cover f U hU)
  intro i
  have := hN i
  exact (SheafOfModules.isFinitePresentation (f ⁻¹ᵁ U i).toScheme.ringCatSheaf).prop_of_iso
    (closedDescent_localIso f U M N e i).symm (hN i)

include hU e in
/-- Descent in the coherent categories, with an pushforward isomorphism on the ambient scheme. This
is the global closed-support step needed to put Cartier restriction and first Tor on the
divisor. -/
lemma exists_coherent_closed_preimage [IsLocallyNoetherian Y] (hN : ∀ i, (N i).IsFinitePresentation) :
    ∃ Q : Coh X, Nonempty ((pushforward f).obj Q.obj ≅ M) := by
  have := closedDescent_coherent f U hU M N e hN
  have := closedDescent_unit_isIso f U hU M N e
  exact ⟨⟨(Scheme.Modules.pullback f).obj M, inferInstance⟩,
    ⟨(asIso ((pullbackPushforwardAdjunction f).unit.app M)).symm⟩⟩
end CoherentGlobal

end

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace ActualSheafTensor
universe u
variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- An isomorphism of sheaves induces a natural tensor isomorphism. -/
def tensorLeftIso {M N : SheafOfModules.{u} (ringSheaf R)} (e : M ≅ N) :
    tensorLeft R M ≅ tensorLeft R N := by
  let S := PresheafOfModules.sheafification (R := ringSheaf R) (𝟙 (ringSheaf R).obj)
  exact Functor.isoWhiskerRight (Functor.isoWhiskerLeft (SheafOfModules.forget (ringSheaf R))
    ((curriedTensor (PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat))).mapIso
      ((SheafOfModules.forget (ringSheaf R)).mapIso e)))
    S

/-- The tensor-with-unit functor is naturally the identity. -/
def tensorUnitLeftIso : tensorLeft R (SheafOfModules.unit _) ≅ 𝟭 _ := by
  have hCounit : IsIso (PresheafOfModules.sheafificationAdjunction
      (R := ringSheaf R) (𝟙 (ringSheaf R).obj)).counit := inferInstance
  let S := PresheafOfModules.sheafification (R := ringSheaf R) (𝟙 (ringSheaf R).obj)
  exact Functor.isoWhiskerRight (Functor.isoWhiskerLeft (SheafOfModules.forget (ringSheaf R))
    (leftUnitorNatIso (PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat))))
    S ≪≫
      @asIso _ _ _ _ (PresheafOfModules.sheafificationAdjunction
        (𝟙 (ringSheaf R).obj)).counit hCounit

/-- Tensoring with the trivial line sheaf is exact by the tensor unit isomorphism. -/
lemma tensorLeft_preservesMonomorphisms_of_unitIso
    (M : SheafOfModules.{u} (ringSheaf R)) (e : M ≅ SheafOfModules.unit _) :
    (tensorLeft R M).PreservesMonomorphisms := by
  let t := tensorLeftIso R e ≪≫ tensorUnitLeftIso R
  exact Functor.PreservesMonomorphisms.of_iso t.symm

end ActualSheafTensor

end

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace ActualSheafTensor
universe u
variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Tensor a morphism of module sheaves on the left. -/
def tensorLeftMap {M N : SheafOfModules.{u} (ringSheaf R)} (f : M ⟶ N) :
    tensorLeft R M ⟶ tensorLeft R N := by
  let S := PresheafOfModules.sheafification (R := ringSheaf R) (𝟙 (ringSheaf R).obj)
  exact Functor.whiskerRight (Functor.whiskerLeft (SheafOfModules.forget (ringSheaf R))
    ((curriedTensor (PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat))).map f.val)) S

/-- The multiplication morphism for a line ideal inside the structure sheaf. Its kernel and cokernel
are the Cartier Tor and restriction objects. -/
def idealAction {L : SheafOfModules.{u} (ringSheaf R)}
    (i : L ⟶ SheafOfModules.unit _) : tensorLeft R L ⟶ 𝟭 _ :=
  tensorLeftMap R i ≫ (tensorUnitLeftIso R).hom

end ActualSheafTensor

end

noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace ActualSheafTensor
universe u
variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u}) (U : C)
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (J.over U) AddCommGrpCat.{u}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Restriction of a module presheaf to the slice category. -/
def presheafOver : PresheafOfModules.{u} (ringSheaf R).obj ⥤
    PresheafOfModules.{u} (ringSheaf (R.over U)).obj :=
  PresheafOfModules.pushforward (𝟙 ((ringSheaf R).over U).obj)

/-- The canonical comparison between sheafification and restriction. -/
def sheafifyOverMap (P : PresheafOfModules.{u} (ringSheaf R).obj) :
    (PresheafOfModules.sheafification (𝟙 (ringSheaf (R.over U)).obj)).obj
      ((presheafOver R U).obj P) ⟶
    ((PresheafOfModules.sheafification (𝟙 (ringSheaf R).obj)).obj P).over U :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf (R.over U)).obj)).symm
    ((presheafOver R U).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit.app P))

/-- The underlying comparison is the established sheafification comparison for a continuous
cocontinuous functor. -/
lemma sheafifyOverMap_toSheaf (P : PresheafOfModules.{u} (ringSheaf R).obj) :
    (SheafOfModules.toSheaf _).map (sheafifyOverMap R U P) =
      ((Over.forget U).pushforwardContinuousSheafificationCompatibility AddCommGrpCat
        (J.over U) J).hom.app P.presheaf := by
  unfold sheafifyOverMap
  erw [PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm]
  apply ((CategoryTheory.sheafificationAdjunction (J.over U) AddCommGrpCat).homEquiv _ _).injective
  erw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  exact ((Over.forget U).toSheafify_pullbackSheafificationCompatibility
    AddCommGrpCat (J.over U) J P.presheaf).symm

instance sheafifyOverMap_isIso (P : PresheafOfModules.{u} (ringSheaf R).obj) :
    IsIso (sheafifyOverMap R U P) := by
  have : IsIso ((SheafOfModules.toSheaf _).map (sheafifyOverMap R U P)) := by
    rw [sheafifyOverMap_toSheaf]
    exact (((Over.forget U).pushforwardContinuousSheafificationCompatibility
      AddCommGrpCat (J.over U) J).app P.presheaf).isIso_hom
  exact isIso_of_reflects_iso (sheafifyOverMap R U P) (SheafOfModules.toSheaf _)

private theorem sheafifyOverMap_adjoint (P : PresheafOfModules.{u} (ringSheaf R).obj) :
    (PresheafOfModules.sheafificationAdjunction
      (𝟙 (ringSheaf (R.over U)).obj)).homEquiv _ _ (sheafifyOverMap R U P) =
      (presheafOver R U).map
        ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit.app P) := by
  erw [PresheafOfModules.sheafificationAdjunction_homEquiv_apply]
  exact (PresheafOfModules.sheafificationHomEquiv _).apply_symm_apply _

lemma sheafifyOverMap_naturality
    {P Q : PresheafOfModules.{u} (ringSheaf R).obj} (f : P ⟶ Q) :
    (PresheafOfModules.sheafification (𝟙 (ringSheaf (R.over U)).obj)).map
        ((presheafOver R U).map f) ≫ sheafifyOverMap R U Q =
      sheafifyOverMap R U P ≫
        (SheafOfModules.overFunctor (ringSheaf R) U).map
          ((PresheafOfModules.sheafification (𝟙 (ringSheaf R).obj)).map f) := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 (ringSheaf (R.over U)).obj)
  apply (adj.homEquiv ((presheafOver R U).obj P)
    (((PresheafOfModules.sheafification (𝟙 (ringSheaf R).obj)).obj Q).over U)).injective
  erw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
  change (presheafOver R U).map f ≫
      adj.homEquiv _ _ (sheafifyOverMap R U Q) =
    adj.homEquiv _ _ (sheafifyOverMap R U P) ≫
      (presheafOver R U).map
        ((SheafOfModules.forget (ringSheaf R)).map
          ((PresheafOfModules.sheafification (𝟙 (ringSheaf R).obj)).map f))
  dsimp only [adj]
  erw [sheafifyOverMap_adjoint R U P, sheafifyOverMap_adjoint R U Q]
  erw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg ((presheafOver R U).map)
    ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit.naturality f)

/-- Sheafification and restriction are naturally isomorphic. -/
def sheafificationCompOver :
    presheafOver R U ⋙ PresheafOfModules.sheafification (𝟙 (ringSheaf (R.over U)).obj) ≅
      PresheafOfModules.sheafification (𝟙 (ringSheaf R).obj) ⋙
        SheafOfModules.overFunctor (ringSheaf R) U :=
  NatIso.ofComponents (fun P => asIso (sheafifyOverMap R U P)) (fun f =>
    sheafifyOverMap_naturality R U f)

/-- Tensor presheaves restrict objectwise exactly. -/
def presheafTensorOverIso (M N : PresheafOfModules.{u} (ringSheaf R).obj) :
    (presheafOver R U).obj (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := R.obj) M N) ≅
      PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := (R.over U).obj)
        ((presheafOver R U).obj M) ((presheafOver R U).obj N) :=
  PresheafOfModules.isoMk (fun V => Iso.refl _)

/-- The tensor sheaf commutes with restriction to every slice site. -/
def tensorOverIso (M N : SheafOfModules.{u} (ringSheaf R)) :
    (tensor R M N).over U ≅ tensor (R.over U) (M.over U) (N.over U) :=
  ((sheafificationCompOver R U).app
    (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := R.obj) M.val N.val)).symm ≪≫
      (PresheafOfModules.sheafification (𝟙 (ringSheaf (R.over U)).obj)).mapIso
        (presheafTensorOverIso R U M.val N.val)


/-- Restriction commutes naturally with tensoring by a fixed presheaf. -/
def presheafTensorCompOverIso (M : PresheafOfModules.{u} (ringSheaf R).obj) :
    CategoryTheory.MonoidalCategory.tensorLeft
        (C := PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat)) M ⋙
        presheafOver R U ≅ presheafOver R U ⋙
      CategoryTheory.MonoidalCategory.tensorLeft
        (C := PresheafOfModules.{u} ((R.over U).obj ⋙ forget₂ CommRingCat RingCat))
        ((presheafOver R U).obj M) :=
  NatIso.ofComponents (fun N => presheafTensorOverIso R U M N) (by
    intro N N' f
    ext V x
    rfl)


end ActualSheafTensor


end

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace ActualSheafTensor
universe u
variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u}) (U : C)
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (J.over U) AddCommGrpCat.{u}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The restriction isomorphism for tensor sheaves is natural in the second variable. This is the
exactness-descent bridge for Cartier twisting. -/
def tensorLeftCompOverIso (M : SheafOfModules.{u} (ringSheaf R)) :
    tensorLeft R M ⋙ SheafOfModules.overFunctor (ringSheaf R) U ≅
      SheafOfModules.overFunctor (ringSheaf R) U ⋙
        tensorLeft (R.over U) (M.over U) := by
  let F := SheafOfModules.forget (ringSheaf R)
  let T := CategoryTheory.MonoidalCategory.tensorLeft
    (C := PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat)) M.val
  let S := PresheafOfModules.sheafification (R := ringSheaf (R.over U))
    (𝟙 (ringSheaf (R.over U)).obj)
  refine Functor.isoWhiskerLeft (F ⋙ T) (sheafificationCompOver R U).symm ≪≫ ?_
  exact Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft F (presheafTensorCompOverIso R U M.val)) S
end ActualSheafTensor

end

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace ActualSheafTensor
universe u
variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

local instance : MonoidalCategory (PresheafOfModules.{u} (ringSheaf R).obj) :=
  inferInstanceAs (MonoidalCategory (PresheafOfModules.{u}
    (R.obj ⋙ forget₂ CommRingCat RingCat)))

/-- The ideal action is the adjoint of ordinary multiplication on pure tensors before
sheafification. -/
lemma idealAction_adjoint {L : SheafOfModules.{u} (ringSheaf R)}
    (i : L ⟶ SheafOfModules.unit _) (M : SheafOfModules.{u} (ringSheaf R)) :
    (PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).homEquiv _ _
      ((idealAction R i).app M) =
    (i.val ▷ M.val) ≫ (λ_ (M.val : PresheafOfModules (R.obj ⋙ forget₂ CommRingCat RingCat))).hom := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)
  apply adj.homEquiv _ _ |>.symm.injective
  dsimp only [adj]
  erw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit, Functor.map_comp]
  change _ ≫ (_ ≫ _) = (_ ≫ _) ≫ _
  exact (Category.assoc _ _ _).symm

private local instance unitSectionSMul (M : SheafOfModules.{u} (ringSheaf R)) (U : Cᵒᵖ) :
    SMul ((SheafOfModules.unit (ringSheaf R)).val.obj U) (M.val.obj U) :=
  show SMul (R.obj.obj U) (M.val.obj U) from (M.val.obj U).isModule.toSMul

/-- Formula on pure tensors, including the sheafification unit. -/
lemma idealAction_pure {L : SheafOfModules.{u} (ringSheaf R)}
    (i : L ⟶ SheafOfModules.unit _) (M : SheafOfModules.{u} (ringSheaf R))
    (U : Cᵒᵖ) (l : L.val.obj U) (m : M.val.obj U) :
    ((idealAction R i).app M).val.app U
      (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit.app
        (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := R.obj) L.val M.val)).app U
          (l ⊗ₜ[R.obj.obj U] m)) = (i.val.app U l) • m := by
  have h := idealAction_adjoint R i M
  erw [Adjunction.homEquiv_unit] at h
  exact congrArg (fun f => f.app U (l ⊗ₜ[R.obj.obj U] m)) h

end ActualSheafTensor

end

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace ActualSheafTensor
universe u
variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U, HasSheafify (J.over U) AddCommGrpCat.{u}]
  [∀ U, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Local trivializations of a rank-one locally free module sheaf. -/
structure LineTrivialization (M : SheafOfModules.{u} (ringSheaf R)) where
  I : Type u
  obj : I → C
  cover : J.CoversTop obj
  iso (i : I) : M.over (obj i) ≅ SheafOfModules.unit _

/-- Tensor by any line bundle preserves monomorphisms, by descent from the unit on its local
trivializing cover. -/
lemma tensorLeft_preservesMonomorphisms_of_line
    (M : SheafOfModules.{u} (ringSheaf R)) (d : LineTrivialization R M) :
    (tensorLeft R M).PreservesMonomorphisms where
  preserves {N P} f := by
    intro hmono
    apply SheafLocality.module_mono_of_coversTop (ringSheaf R) d.cover
    intro i
    let V := d.obj i
    let hTensor : (tensorLeft (R.over V) (M.over V)).PreservesMonomorphisms :=
      tensorLeft_preservesMonomorphisms_of_unitIso (R.over V) (M.over V) (d.iso i)
    let hOver : (SheafOfModules.overFunctor.{u} (ringSheaf R) V).PreservesMonomorphisms := by
      constructor
      intro A B g hg
      have : PreservesFiniteLimits (SheafOfModules.forget.{u} (ringSheaf R)) :=
        SheafOfModules.Finite.forgetPreservesFiniteLimits (ringSheaf R)
      have : (SheafOfModules.forget.{u} (ringSheaf R)).PreservesMonomorphisms :=
        preservesMonomorphisms_of_preservesLimitsOfShape _
      have : Mono g.val := inferInstanceAs (Mono ((SheafOfModules.forget.{u} (ringSheaf R)).map g))
      apply (SheafOfModules.forget.{u} ((ringSheaf R).over V)).mono_of_mono_map
      apply PresheafOfModules.mono_of_injective
      intro W
      exact PresheafOfModules.injective_of_mono g.val (Opposite.op W.unop.left)
    let hLocalComposite : (SheafOfModules.overFunctor.{u} (ringSheaf R) V ⋙
        tensorLeft (R.over V) (M.over V)).PreservesMonomorphisms :=
      @Functor.preservesMonomorphisms_comp _ _ _ _ _ _ _ _ hOver hTensor
    let hComposite : (tensorLeft R M ⋙ SheafOfModules.overFunctor.{u} (ringSheaf R) V).PreservesMonomorphisms :=
      (Functor.PreservesMonomorphisms.iso_iff (tensorLeftCompOverIso R V M)).mpr
        hLocalComposite
    exact (inferInstance : Mono
      ((tensorLeft R M ⋙ SheafOfModules.overFunctor.{u} (ringSheaf R) V).map f))

/-- Tensoring by a line bundle is actually exact throughout the category of module sheaves. Right
exactness comes from the proved tensor-Hom adjunction. -/
lemma tensorLeft_preservesHomology_of_line
    (M : SheafOfModules.{u} (ringSheaf R)) (d : LineTrivialization R M) :
    (tensorLeft R M).PreservesHomology := by
  have := tensorLeft_preservesMonomorphisms_of_line R M d
  exact Functor.preservesHomology_of_preservesMonos_and_cokernels _

end ActualSheafTensor

end

end OAI
