import OAI.AlgebraicGeometry.SurfaceCones.CoherentGlobalHom

namespace OAI

section

noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped TensorProduct
namespace CoherentModelActual
open CoherentDual Scheme.Modules
variable {A B C : CommRingCat.{0}} [IsNoetherianRing B]
  (f : A ⟶ B) (M : ModuleCat A) [Module.Finite A M]

/-- The actual section module of a restriction of the affine double-dual
model extension, expressed as an honest scalar extension of the double dual. -/
def affineEPullbackGammaIso (q : B ⟶ C) :
    (moduleSpecΓFunctor (R := C)).obj
      ((Scheme.Modules.pullback (Spec.map q)).obj (E (Spec.map f) M)) ≅
      (ModuleCat.extendScalars q.hom).obj
        (ModuleCat.of B (Module.Dual B (Module.Dual B (affineModule f M)))) :=
  moduleSpecΓFunctor.mapIso ((Scheme.Modules.pullback (Spec.map q)).mapIso
    (affineEIso f M) ≪≫ (AffinePullback.pullbackTildeIso q).app _) ≪≫
    (tilde.toTildeΓNatIso.app _).symm

variable [IsDomain A] [IsNoetherianRing A] [IsDomain B]
  [Module.IsTorsionFree A M] [Nontrivial M]

omit [IsNoetherianRing B] [IsDomain B] in
lemma affineDoubleDual_nontrivial (hf : Function.Injective f) :
    Nontrivial (Module.Dual B (Module.Dual B (affineModule f M))) := by
  let : Algebra A B := f.hom.toAlgebra
  have := Module.finitePresentation_of_finite A M
  exact FiniteDomainDual.doubleDual_baseChange_nontrivial B hf

/-- The arbitrary ungraded input module gives a NONZERO restriction of its
literal affine model extension at every prime divisor. -/
theorem affineE_prime_restriction_nontrivial (hf : Function.Injective f)
    (p : Ideal B) [p.IsPrime] :
    let q : B ⟶ CommRingCat.of (B ⧸ p) := CommRingCat.ofHom (Ideal.Quotient.mk p)
    Nontrivial ((moduleSpecΓFunctor (R := CommRingCat.of (B ⧸ p))).obj
      ((Scheme.Modules.pullback (Spec.map q)).obj (E (Spec.map f) M))) := by
  dsimp only
  let q : B ⟶ CommRingCat.of (B ⧸ p) := CommRingCat.ofHom (Ideal.Quotient.mk p)
  let N := Module.Dual B (Module.Dual B (affineModule f M))
  have : Nontrivial N := affineDoubleDual_nontrivial f M hf
  have : IsNoetherian B N := isNoetherian_linearMap B B (Module.Dual B (affineModule f M))
  have : Module.Finite B N := ⟨IsNoetherian.noetherian ⊤⟩
  have : Nontrivial ((ModuleCat.extendScalars q.hom).obj (ModuleCat.of B N)) :=
    FiniteDomainDual.prime_fiber_nontrivial (M := N) p
  exact (affineEPullbackGammaIso f M q).toLinearEquiv.nontrivial

/-- The restriction has strictly positive generic rank on the integral
Cartier divisor. Positivity is deduced from M≠0, not assumed for the sheaf. -/
theorem affineE_cartier_rank_pos (hf : Function.Injective f)
    (t : B) (ht : IsSMulRegular B t) [(Ideal.span ({t} : Set B)).IsPrime] :
    let q : B ⟶ CommRingCat.of (B ⧸ Ideal.span ({t} : Set B)) :=
      CommRingCat.ofHom (Ideal.Quotient.mk _)
    0 < Module.finrank (B ⧸ Ideal.span ({t} : Set B))
      ((moduleSpecΓFunctor (R := CommRingCat.of (B ⧸ Ideal.span ({t} : Set B)))).obj
        ((Scheme.Modules.pullback (Spec.map q)).obj (E (Spec.map f) M))) := by
  dsimp only
  let p := Ideal.span ({t} : Set B)
  let q : B ⟶ CommRingCat.of (B ⧸ p) := CommRingCat.ofHom (Ideal.Quotient.mk p)
  have := affineE_prime_restriction_nontrivial f M hf p
  have := affineE_cartier_torsionFree f M t ht
  let N := Module.Dual B (Module.Dual B (affineModule f M))
  have : IsNoetherian B N := isNoetherian_linearMap B B (Module.Dual B (affineModule f M))
  have : Module.Finite B N := ⟨IsNoetherian.noetherian ⊤⟩
  have : Module.Finite (B ⧸ p) ((ModuleCat.extendScalars q.hom).obj (ModuleCat.of B N)) := by
    change Module.Finite (B ⧸ p) ((B ⧸ p) ⊗[B] N)
    infer_instance
  have : Module.Finite (B ⧸ p)
      ((moduleSpecΓFunctor (R := CommRingCat.of (B ⧸ p))).obj
        ((Scheme.Modules.pullback (Spec.map q)).obj (E (Spec.map f) M))) :=
    Module.Finite.of_surjective (affineEPullbackGammaIso f M q).toLinearEquiv.symm.toLinearMap
      (affineEPullbackGammaIso f M q).toLinearEquiv.symm.surjective
  exact Module.finrank_pos
end CoherentModelActual

end

end

section
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace CoherentDual

/-- Sections of an actual sheaf dual on an integral scheme are torsion-free.
This does not postulate a torsion-free coherent object: it is proved pointwise
on the local linear transformations defining the internal Hom. -/
lemma dual_sections_torsionFree {X : Scheme.{0}} [IsIntegral X]
    (M : X.Modules) (U : X.Opens) :
    @Module.IsTorsionFree Γ(X, U)
      ((homSheaf.{0,0,0,0} X.sheaf M (SheafOfModules.unit _)).val.obj (op U)) _ _
      ((homSheaf.{0,0,0,0} X.sheaf M (SheafOfModules.unit _)).val.obj (op U)).isModule := by
  let : Module Γ(X, U)
      ((homSheaf.{0,0,0,0} X.sheaf M (SheafOfModules.unit _)).val.obj (op U)) :=
    ((homSheaf.{0,0,0,0} X.sheaf M (SheafOfModules.unit _)).val.obj (op U)).isModule
  refine @Module.IsTorsionFree.mk _ _ _ _ this ?_
  · intro r hr f g hfg
    apply Subtype.ext
    apply local_ext
    intro V x
    by_cases hV : Nonempty V.unop.left
    · let := hV
      have hU : Nonempty U := by
        obtain ⟨v⟩ := hV
        exact ⟨⟨v.1, leOfHom V.unop.hom v.2⟩⟩
      let := hU
      have hr0 : r ≠ 0 := isRegular_iff_ne_zero.mp hr
      have hs : X.presheaf.map V.unop.hom.op r ≠ 0 := by
        intro hs
        exact hr0 (map_injective_of_isIntegral X V.unop.hom (by simpa using hs))
      let a : Γ(X, V.unop.left) := localApp f.val V x
      let b : Γ(X, V.unop.left) := localApp g.val V x
      let s : Γ(X, V.unop.left) := X.presheaf.map V.unop.hom.op r
      have hh := congrArg (fun z => localApp z.val V x) hfg
      change s * a = s * b at hh
      exact mul_left_cancel₀ (M₀ := Γ(X, V.unop.left)) hs hh
    · have hz : V.unop.left = ⊥ := by
        ext v
        change v ∈ V.unop.left ↔ False
        exact ⟨fun hv => hV ⟨⟨v, hv⟩⟩, False.elim⟩
      have : Subsingleton Γ(X, V.unop.left) :=
        CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hz)
      exact Subsingleton.elim (α := Γ(X, V.unop.left)) _ _

end CoherentDual

end

end

section
noncomputable section
open CategoryTheory CategoryTheory.Functor Opposite
namespace ModuleReindex
universe u
variable {C D : Type u} [Category.{u} C] [Category.{u} D]

/-- Reindexing along an equivalence does not discard module morphisms. The
linearity of the inverse natural transformation is transported through the
counit isomorphism, rather than postulated. -/
instance pushforwardZero_full (F : C ⥤ D) [F.IsEquivalence]
    (R : Dᵒᵖ ⥤ RingCat.{u}) : (PresheafOfModules.pushforward₀.{u} F R).Full where
  map_surjective {M N} f := by
    let W := (whiskeringLeft Cᵒᵖ Dᵒᵖ AddCommGrpCat.{u}).obj F.op
    let g : M.presheaf ⟶ N.presheaf :=
      W.preimage ((PresheafOfModules.toPresheaf _).map f)
    have hg (U : Cᵒᵖ) : g.app (F.op.obj U) =
        (forget₂ _ AddCommGrpCat).map (f.app U) :=
      congrArg (fun z => z.app U) (W.map_preimage (X := M.presheaf) (Y := N.presheaf) ((PresheafOfModules.toPresheaf _).map f))
    let g' : M ⟶ N := PresheafOfModules.homMk g (by
      intro U r x
      let e : F.op.obj (F.asEquivalence.op.inverse.obj U) ≅ U :=
        F.asEquivalence.op.counitIso.app U
      apply (ConcreteCategory.bijective_of_isIso (N.presheaf.map e.inv)).1
      have hn (y : M.obj U) :
          N.map e.inv ((g.app U).hom y) =
            (g.app (F.op.obj (F.asEquivalence.op.inverse.obj U))).hom (M.map e.inv y) :=
        (ConcreteCategory.congr_hom (g.naturality e.inv) y).symm
      change N.map e.inv ((g.app U).hom (r • x)) =
        N.map e.inv (r • (g.app U).hom x)
      erw [hn, N.map_smul, M.map_smul, hn, hg]
      exact (f.app _).hom.map_smul (R.map e.inv r) (M.map e.inv x))
    refine ⟨g', ?_⟩
    ext U x
    exact ConcreteCategory.congr_hom (hg U) x

instance pushforwardZero_faithful (F : C ⥤ D) [F.IsEquivalence]
    (R : Dᵒᵖ ⥤ RingCat.{u}) : (PresheafOfModules.pushforward₀.{u} F R).Faithful where
  map_injective {M N} f g h := by
    apply (PresheafOfModules.toPresheaf R).map_injective
    apply ((whiskeringLeft Cᵒᵖ Dᵒᵖ AddCommGrpCat.{u}).obj F.op).map_injective
    exact congrArg ((PresheafOfModules.toPresheaf _).map) h

/-- Restriction through an isomorphism of the coefficient presheaves is full. -/
instance restrictScalars_full {R S : Cᵒᵖ ⥤ RingCat.{u}}
    (φ : R ⟶ S) [IsIso φ] : (PresheafOfModules.restrictScalars.{u} φ).Full where
  map_surjective {M N} f := by
    let g₀ : M.presheaf ⟶ N.presheaf := (PresheafOfModules.toPresheaf R).map f
    let g : M ⟶ N := PresheafOfModules.homMk g₀ (by
        intro U r x
        let s := (inv φ).app U r
        have hs : φ.app U s = r := by
          exact ConcreteCategory.congr_hom ((asIso φ).inv_hom_id_app U) r
        have hl := (f.app U).hom.map_smul s x
        change (g₀.app U).hom (φ.app U s • x) = φ.app U s • (g₀.app U).hom x at hl
        simpa only [hs] using hl)
    exact ⟨g, by ext U x; rfl⟩

/-- Actual reindexing plus coefficient isomorphism is fully faithful. -/
def pushforward_fullyFaithful (F : C ⥤ D) [F.IsEquivalence]
    {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}}
    (φ : S ⟶ F.op ⋙ R) [IsIso φ] :
    (PresheafOfModules.pushforward.{u} φ).FullyFaithful := by
  change (PresheafOfModules.pushforward₀ F R ⋙ PresheafOfModules.restrictScalars φ).FullyFaithful
  exact Functor.FullyFaithful.ofFullyFaithful _
end ModuleReindex

end

end

section
noncomputable section
open CategoryTheory Opposite
namespace CoherentDual
section Reindex
universe u
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  (F : C ⥤ D) {R : Dᵒᵖ ⥤ CommRingCat.{u}} {S : Cᵒᵖ ⥤ CommRingCat.{u}}
  (φ : S ⟶ F.op ⋙ R)
  (M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))

def homReindexApp (X : C) :
    ((PresheafOfModules.pushforward (Functor.whiskerRight φ (forget₂ CommRingCat RingCat))).obj
      (homPresheaf (R := R) (M := M) (N := N))).obj (op X) →ₗ[S.obj (op X)]
    (homPresheaf (R := S)
      (M := (PresheafOfModules.pushforward (Functor.whiskerRight φ (forget₂ CommRingCat RingCat))).obj M)
      (N := (PresheafOfModules.pushforward (Functor.whiskerRight φ (forget₂ CommRingCat RingCat))).obj N)).obj (op X) where
  toFun f := ⟨Functor.whiskerLeft (Over.post (X := X) F).op f.val,
    fun Y r x => f.property ((Over.post F).op.obj Y) (φ.app (op Y.unop.left) r) x⟩
  map_add' f g := rfl
  map_smul' r f := by
    apply Subtype.ext
    apply local_ext
    intro Y x
    exact congrArg (fun s : R.obj (op ((Over.post (X := X) F).obj Y.unop).left) =>
      s • localApp f.val ((Over.post F).op.obj Y) x)
      (ConcreteCategory.congr_hom (φ.naturality Y.unop.hom.op) r).symm

lemma homReindexApp_bijective [IsIso φ] (X : C)
    [(Over.post (X := X) F).IsEquivalence] :
    Function.Bijective (homReindexApp F φ M N X) := by
  let φ₀ := Functor.whiskerRight φ (forget₂ CommRingCat RingCat)
  let ψ := Functor.whiskerLeft (Over.forget X).op φ₀
  have hψ : IsIso ψ := (Functor.isoWhiskerLeft (Over.forget X).op
    (Functor.isoWhiskerRight (asIso φ) (forget₂ CommRingCat RingCat))).isIso_hom
  let FF := @ModuleReindex.pushforward_fullyFaithful _ _ _ _ (Over.post (X := X) F) _
    ((Over.forget (F.obj X)).op ⋙ (R ⋙ forget₂ CommRingCat RingCat))
    ((Over.forget X).op ⋙ (S ⋙ forget₂ CommRingCat RingCat)) ψ hψ
  let e := (localHomEquiv (R := R) (M := M) (N := N) (F.obj X)).trans
    (FF.homEquiv.trans (localHomEquiv (R := S)
      (M := (PresheafOfModules.pushforward φ₀).obj M)
      (N := (PresheafOfModules.pushforward φ₀).obj N) X).symm)
  change Function.Bijective e
  exact e.bijective

/-- Internal linear Hom is preserved by coefficient isomorphisms and a
reindexing functor that is an equivalence on every slice. -/
def homReindexPresheafIso [IsIso φ]
    (hF : ∀ X, (Over.post (X := X) F).IsEquivalence) :
    (PresheafOfModules.pushforward (Functor.whiskerRight φ (forget₂ CommRingCat RingCat))).obj
      (homPresheaf (R := R) (M := M) (N := N)) ≅
    homPresheaf (R := S)
      (M := (PresheafOfModules.pushforward (Functor.whiskerRight φ (forget₂ CommRingCat RingCat))).obj M)
      (N := (PresheafOfModules.pushforward (Functor.whiskerRight φ (forget₂ CommRingCat RingCat))).obj N) := by
  have (X : C) : (Over.post (X := X) F).IsEquivalence := hF X
  exact PresheafOfModules.isoMk (fun X =>
    (LinearEquiv.ofBijective (homReindexApp F φ M N X.unop)
      (homReindexApp_bijective F φ M N X.unop)).toModuleIso) (by
        intro X Y g
        ext f
        apply Subtype.ext
        apply local_ext
        intro Z x
        change localApp f.val (op (Over.mk (F.map Z.unop.hom ≫ F.map g.unop))) x =
          localApp f.val (op (Over.mk (F.map (Z.unop.hom ≫ g.unop)))) x
        rw [F.map_comp])
end Reindex
end CoherentDual

end

end

section
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace ActualSheafTensor
universe u
variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

abbrev ringSheaf : Sheaf J RingCat.{u} := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R

local instance : MonoidalCategory (PresheafOfModules.{u} (ringSheaf R).obj) :=
  inferInstanceAs (MonoidalCategory (PresheafOfModules.{u}
    (R.obj ⋙ forget₂ CommRingCat RingCat)))

/-- The actual tensor sheaf: sheafification of the objectwise tensor product
of presheaves of modules. It will provide the Cartier line-bundle twists. -/
def tensor (M N : SheafOfModules.{u} (ringSheaf R)) : SheafOfModules.{u} (ringSheaf R) :=
  (PresheafOfModules.sheafification (𝟙 (ringSheaf R).obj)).obj (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := R.obj) M.val N.val)

/-- Tensoring with a fixed sheaf, on both objects and morphisms. -/
def tensorLeft (M : SheafOfModules.{u} (ringSheaf R)) :
    SheafOfModules.{u} (ringSheaf R) ⥤ SheafOfModules.{u} (ringSheaf R) :=
  SheafOfModules.forget _ ⋙ CategoryTheory.MonoidalCategory.tensorLeft (M.val : PresheafOfModules (R.obj ⋙ forget₂ CommRingCat RingCat)) ⋙
    PresheafOfModules.sheafification (𝟙 (ringSheaf R).obj)

/-- Tensoring the structure sheaf is canonically the identity, not a
postulated operation on formal Chern data. -/
def leftUnitIso (M : SheafOfModules.{u} (ringSheaf R)) :
    tensor R (SheafOfModules.unit _) M ≅ M :=
  (PresheafOfModules.sheafification (𝟙 (ringSheaf R).obj)).mapIso (λ_ (M.val : PresheafOfModules (R.obj ⋙ forget₂ CommRingCat RingCat))) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).counit).app M

/-- The analogous canonical right unit isomorphism. -/
def rightUnitIso (M : SheafOfModules.{u} (ringSheaf R)) :
    tensor R M (SheafOfModules.unit _) ≅ M :=
  (PresheafOfModules.sheafification (𝟙 (ringSheaf R).obj)).mapIso (ρ_ (M.val : PresheafOfModules (R.obj ⋙ forget₂ CommRingCat RingCat))) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).counit).app M

end ActualSheafTensor

end

end

section
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace CoherentDual
universe u
variable {C : Type u} [Category.{u} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
  {M N P : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)}

/-- A bilinear map of actual presheaves defines local linear maps by restricting
its second argument. -/
def tensorCurryAt (f : M ⊗ N ⟶ P) (U : C) (y : N.obj (op U)) (V : Over U) :
    M.obj (op V.left) →+ P.obj (op V.left) where
  toFun x := f.app (op V.left) (x ⊗ₜ[R.obj (op V.left)] N.map V.hom.op y)
  map_zero' := by
    erw [TensorProduct.zero_tmul, map_zero]
  map_add' _ _ := by
    erw [TensorProduct.add_tmul, map_add]

/-- The sectionwise tensor-Hom adjunction on a slice. -/
def tensorCurryLocal (f : M ⊗ N ⟶ P) (U : C) (y : N.obj (op U)) :
    linearLocalHom (R := R) (M := M) (N := P) U := by
  refine ⟨{ app := fun V => AddCommGrpCat.ofHom (tensorCurryAt f U y V.unop)
            naturality := ?_ }, ?_⟩
  · intro V W g
    ext x
    change f.app (op W.unop.left)
        (M.map g.unop.left.op x ⊗ₜ[R.obj (op W.unop.left)] N.map W.unop.hom.op y) =
      P.map g.unop.left.op (f.app (op V.unop.left)
        (x ⊗ₜ[R.obj (op V.unop.left)] N.map V.unop.hom.op y))
    have h := PresheafOfModules.naturality_apply f g.unop.left.op
      (x ⊗ₜ[R.obj (op V.unop.left)] N.map V.unop.hom.op y)
    erw [PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul] at h
    rw [← h]
    congr 2
    rw [← PresheafOfModules.map_comp_apply, ← op_comp, Over.w]
  · intro V a x
    change f.app (op V.unop.left)
      ((a • x) ⊗ₜ[R.obj (op V.unop.left)] N.map V.unop.hom.op y) =
      a • f.app (op V.unop.left)
        (x ⊗ₜ[R.obj (op V.unop.left)] N.map V.unop.hom.op y)
    erw [← TensorProduct.smul_tmul', (f.app _).hom.map_smul]

def tensorCurryLinear (f : M ⊗ N ⟶ P) (U : C) :
    N.obj (op U) →ₗ[R.obj (op U)] linearLocalHom (R := R) (M := M) (N := P) U where
  toFun := tensorCurryLocal f U
  map_add' y z := by
    apply Subtype.ext
    apply local_ext
    intro V x
    change f.app (op V.unop.left) (x ⊗ₜ[R.obj (op V.unop.left)] N.map V.unop.hom.op (y+z)) = _
    erw [map_add, TensorProduct.tmul_add, map_add]
    rfl
  map_smul' a y := by
    apply Subtype.ext
    apply local_ext
    intro V x
    change f.app (op V.unop.left) (x ⊗ₜ[R.obj (op V.unop.left)] N.map V.unop.hom.op (a • y)) =
      R.map V.unop.hom.op a • f.app (op V.unop.left)
        (x ⊗ₜ[R.obj (op V.unop.left)] N.map V.unop.hom.op y)
    have hy : (N.map V.unop.hom.op (a • y) : N.obj (op V.unop.left)) =
        (R.map V.unop.hom.op a) • (N.map V.unop.hom.op y : N.obj (op V.unop.left)) :=
      N.map_smul _ a y
    rw [hy]
    let b : R.obj (op V.unop.left) := R.map V.unop.hom.op a
    let z : N.obj (op V.unop.left) := N.map V.unop.hom.op y
    let q : TensorProduct (R.obj (op V.unop.left)) (M.obj (op V.unop.left)) (N.obj (op V.unop.left))
        →ₗ[R.obj (op V.unop.left)] P.obj (op V.unop.left) := (f.app _).hom
    change q (x ⊗ₜ[R.obj (op V.unop.left)] (b • z)) =
      b • q (x ⊗ₜ[R.obj (op V.unop.left)] z)
    rw [TensorProduct.tmul_smul, q.map_smul]

/-- Currying is a morphism of genuine presheaves of modules. -/
def tensorCurry (f : M ⊗ N ⟶ P) : N ⟶ homPresheaf (R := R) (M := M) (N := P) where
  app U := ModuleCat.ofHom (tensorCurryLinear f U.unop)
  naturality {U V} g := by
    ext y
    apply Subtype.ext
    apply local_ext
    intro W x
    change f.app (op W.unop.left)
        (x ⊗ₜ[R.obj (op W.unop.left)] N.map W.unop.hom.op (N.map g y)) =
      f.app (op W.unop.left)
        (x ⊗ₜ[R.obj (op W.unop.left)] N.map (W.unop.hom ≫ g.unop).op y)
    rw [op_comp, PresheafOfModules.map_comp_apply]
    rfl

/-- Evaluation gives the inverse to currying on each object. -/
def tensorUncurryApp (f : N ⟶ homPresheaf (R := R) (M := M) (N := P)) (U : Cᵒᵖ) :
    M.obj U ⊗ N.obj U ⟶ P.obj U :=
  ModuleCat.MonoidalCategory.tensorLift (R := R.obj U)
    (fun x y => localApp (f.app U y).val (op (Over.mk (𝟙 U.unop))) x)
    (fun x z y => (localApp (f.app U y).val (op (Over.mk (𝟙 U.unop)))).map_add x z)
    (fun a x y => (f.app U y).property (op (Over.mk (𝟙 U.unop))) a x)
    (fun x y z => by
      have h := (f.app U).hom.map_add y z
      change localApp (f.app U (y+z)).val (op (Over.mk (𝟙 U.unop))) x = _
      rw [h]
      rfl)
    (fun a x y => by
      have h := (f.app U).hom.map_smul a y
      change localApp (f.app U (a • y)).val (op (Over.mk (𝟙 U.unop))) x = _
      rw [h]
      change (R.map (𝟙 U.unop).op a) • localApp (f.app U y).val (op (Over.mk (𝟙 U.unop))) x = _
      rw [op_id, Functor.map_id_apply])

@[simp] lemma tensorUncurryApp_tmul
    (f : N ⟶ homPresheaf (R := R) (M := M) (N := P))
    (U : Cᵒᵖ) (x : M.obj U) (y : N.obj U) :
    tensorUncurryApp f U (x ⊗ₜ[R.obj U] y) =
      localApp (f.app U y).val (op (Over.mk (𝟙 U.unop))) x := rfl

/-- Uncurrying is compatible with restriction maps. -/
def tensorUncurry (f : N ⟶ homPresheaf (R := R) (M := M) (N := P)) : M ⊗ N ⟶ P where
  app U := tensorUncurryApp f U
  naturality {U V} g := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro x y
    change tensorUncurryApp f V ((M ⊗ N).map g (x ⊗ₜ[R.obj U] y)) =
      P.map g (tensorUncurryApp f U (x ⊗ₜ[R.obj U] y))
    have ht := PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul
      (R := R) (M₁ := M) (M₂ := N) g x y
    erw [ht]
    erw [tensorUncurryApp_tmul f V (M.map g x) (N.map g y),
      tensorUncurryApp_tmul f U x y]
    change localApp (f.app V (N.map g y)).val (op (Over.mk (𝟙 V.unop)))
        (M.map g x) =
      P.map g (localApp (f.app U y).val (op (Over.mk (𝟙 U.unop))) x)
    have h := PresheafOfModules.naturality_apply f g y
    change f.app V (N.map g y) = _ at h
    rw [h]
    change localApp (f.app U y).val (op (Over.mk ((𝟙 V.unop) ≫ g.unop)))
      (M.map g x) = _
    rw [Category.id_comp]
    let k : Over.mk g.unop ⟶ Over.mk (𝟙 U.unop) := Over.homMk g.unop (by simp)
    exact (local_naturality (f.app U y).val k x).symm

lemma tensorUncurryCurry (f : M ⊗ N ⟶ P) : tensorUncurry (tensorCurry f) = f := by
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  change f.app U (x ⊗ₜ[R.obj U] N.map (𝟙 U.unop).op y) = f.app U (x ⊗ₜ[R.obj U] y)
  simp only [op_id, PresheafOfModules.map_id]
  rfl

lemma tensorCurryUncurry (f : N ⟶ homPresheaf (R := R) (M := M) (N := P)) :
    tensorCurry (tensorUncurry f) = f := by
  ext U y
  apply Subtype.ext
  apply local_ext
  intro V x
  change localApp (f.app (op V.unop.left) (N.map V.unop.hom.op y)).val
    (op (Over.mk (𝟙 V.unop.left))) x = localApp (f.app U y).val V x
  have h := PresheafOfModules.naturality_apply f V.unop.hom.op y
  change f.app (op V.unop.left) (N.map V.unop.hom.op y) = _ at h
  rw [h]
  change localApp (f.app U y).val (op (Over.mk ((𝟙 V.unop.left) ≫ V.unop.hom))) x = _
  rw [Category.id_comp]
  rfl

/-- Actual tensor-Hom equivalence for presheaves. -/
def tensorHomEquiv : (M ⊗ N ⟶ P) ≃ (N ⟶ homPresheaf (R := R) (M := M) (N := P)) where
  toFun := tensorCurry
  invFun := tensorUncurry
  left_inv := tensorUncurryCurry
  right_inv := tensorCurryUncurry

end CoherentDual

end

end

section
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace CoherentDual
universe u
variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (M N P : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))

/-- The tensor-Hom equivalence for actual module sheaves. The domain is the
sheafification of the genuine sectionwise tensor product, and the codomain
is the sheaf of local linear transformations proved to satisfy descent. -/
def sheafTensorHomEquiv :
    (ActualSheafTensor.tensor R M N ⟶ P) ≃ (N ⟶ homSheaf R M P) :=
  ((PresheafOfModules.sheafificationAdjunction
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).homEquiv _ _).trans
    ((tensorHomEquiv (R := R.obj) (M := M.val) (N := N.val) (P := P.val)).trans
      ((SheafOfModules.fullyFaithfulForget _).homEquiv (X := N) (Y := homSheaf R M P)).symm)

lemma tensorCurry_naturality_left
    {R' : Cᵒᵖ ⥤ CommRingCat.{u}}
    {M' N' N'' P' : PresheafOfModules.{u} (R' ⋙ forget₂ CommRingCat RingCat)}
    (f : N'' ⟶ N') (g : M' ⊗ N' ⟶ P') :
    tensorCurry ((CategoryTheory.MonoidalCategory.tensorLeft M').map f ≫ g) =
      f ≫ tensorCurry g := by
  ext U y
  apply Subtype.ext
  apply local_ext
  intro V x
  change g.app (op V.unop.left)
      (x ⊗ₜ[R'.obj (op V.unop.left)] f.app (op V.unop.left) (N''.map V.unop.hom.op y)) =
    g.app (op V.unop.left)
      (x ⊗ₜ[R'.obj (op V.unop.left)] N'.map V.unop.hom.op (f.app U y))
  rw [PresheafOfModules.naturality_apply]

lemma sheafTensorHomEquiv_val
    (g : ActualSheafTensor.tensor R M N ⟶ P) :
    (sheafTensorHomEquiv R M N P g).val =
      tensorCurry (R := R.obj) (M := M.val) (N := N.val) (P := P.val)
        ((PresheafOfModules.sheafificationAdjunction
          (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).homEquiv
          (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := R.obj) M.val N.val) P g) := rfl

lemma sheafTensorHomEquiv_naturality_left
    {N' : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (f : N' ⟶ N) (g : ActualSheafTensor.tensor R M N ⟶ P) :
    sheafTensorHomEquiv R M N' P ((ActualSheafTensor.tensorLeft R M).map f ≫ g) =
      f ≫ sheafTensorHomEquiv R M N P g := by
  apply (SheafOfModules.forget _).map_injective
  simp only [SheafOfModules.forget_map, SheafOfModules.comp_val,
    sheafTensorHomEquiv_val]
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  let F := CategoryTheory.MonoidalCategory.tensorLeft
    (C := PresheafOfModules (R.obj ⋙ forget₂ CommRingCat RingCat)) (M.val : PresheafOfModules (R.obj ⋙ forget₂ CommRingCat RingCat))
  have h := adj.homEquiv_naturality_left (F.map f.val) g
  erw [h]
  exact tensorCurry_naturality_left (R' := R.obj) (M' := M.val)
    (N' := N.val) (N'' := N'.val) (P' := P.val) f.val (adj.homEquiv _ _ g)

/-- Actual tensor sheaves are a left adjoint, so tensoring is right exact. -/
def tensorHomAdjunction : ActualSheafTensor.tensorLeft R M ⊣
    Adjunction.rightAdjointOfEquiv (F := ActualSheafTensor.tensorLeft R M) (fun N P => sheafTensorHomEquiv R M N P)
      (fun _ _ _ f g => sheafTensorHomEquiv_naturality_left R M _ _ f g) :=
  Adjunction.adjunctionOfEquivRight (F := ActualSheafTensor.tensorLeft R M) (fun N P => sheafTensorHomEquiv R M N P)
    (fun _ _ _ f g => sheafTensorHomEquiv_naturality_left R M _ _ f g)

instance tensorLeft_preservesColimits : PreservesColimits (ActualSheafTensor.tensorLeft R M) :=
  (tensorHomAdjunction R M).leftAdjoint_preservesColimits

end CoherentDual

end

end

section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace CoherentDual
open Scheme.Modules

instance opensPost_essSurj {X Y : Scheme.{0}} (f : X ⟶ Y) [IsOpenImmersion f]
    (U : X.Opens) : (Over.post (X := U) f.opensFunctor).EssSurj where
  mem_essImage V := by
    have hpre : f ⁻¹ᵁ V.left ≤ U := by
      have h := leOfHom ((TopologicalSpace.Opens.map f.base).map V.hom)
      exact h.trans (le_of_eq (f.preimage_image_eq U))
    have himage : f ''ᵁ (f ⁻¹ᵁ V.left) = V.left := by
      rw [f.image_preimage_eq_opensRange_inf]
      exact inf_eq_right.mpr ((leOfHom V.hom).trans (f.image_le_opensRange U))
    refine ⟨Over.mk (homOfLE hpre), ⟨Over.isoMk (eqToIso himage)⟩⟩

instance opensPost_isEquivalence {X Y : Scheme.{0}} (f : X ⟶ Y) [IsOpenImmersion f]
    (U : X.Opens) : (Over.post (X := U) f.opensFunctor).IsEquivalence := {}

/-- The actual internal linear Hom commutes with restriction to an open
subscheme, including the non-definitional coefficient-ring isomorphism. -/
def homSchemeRestrictionIso {X Y : Scheme.{0}} (f : X ⟶ Y) [IsOpenImmersion f]
    (M N : Y.Modules) :
    (restrictFunctor f).obj (homSheaf Y.sheaf M N) ≅
      homSheaf X.sheaf ((restrictFunctor f).obj M) ((restrictFunctor f).obj N) := by
  let φ : X.presheaf ⟶ f.opensFunctor.op ⋙ Y.presheaf :=
    { app U := (f.appIso U.unop).inv }
  have : IsIso φ := NatIso.isIso_of_isIso_app _
  apply (SheafOfModules.fullyFaithfulForget _).preimageIso
  exact homReindexPresheafIso f.opensFunctor φ M.val N.val (fun U => inferInstance)

/-- Covariant functoriality in the target of the actual internal Hom. -/
abbrev homSheafCovFunctor {C : Type} [Category C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{0})
    [HasSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}]
    (M : SheafOfModules.{0} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :=
  Adjunction.rightAdjointOfEquiv (F := ActualSheafTensor.tensorLeft R M)
    (fun N P => sheafTensorHomEquiv R M N P)
    (fun _ _ _ f g => sheafTensorHomEquiv_naturality_left R M _ _ f g)

/-- In particular the genuine coherent dual restricts to the genuine dual
of the restricted sheaf; no formal identification of section rings is used. -/
def dualSchemeRestrictionIso {X Y : Scheme.{0}} (f : X ⟶ Y) [IsOpenImmersion f]
    (M : Y.Modules) :
    (restrictFunctor f).obj (homSheaf Y.sheaf M (SheafOfModules.unit _)) ≅
      homSheaf X.sheaf ((restrictFunctor f).obj M) (SheafOfModules.unit _) :=
  homSchemeRestrictionIso f M (SheafOfModules.unit _) ≪≫
    (homSheafCovFunctor X.sheaf ((restrictFunctor f).obj M)).mapIso (restrictUnitIso f)
end CoherentDual

end

end

section

noncomputable section
open CategoryTheory AlgebraicGeometry
namespace CoherentModelActual
open CoherentDual Scheme.Modules

/-- Functoriality of the literal structure-sheaf double dual. -/
def doubleDualIso {X : Scheme.{0}} {M N : X.Modules} (e : M ≅ N) :
    homSheaf X.sheaf (homSheaf X.sheaf M (SheafOfModules.unit _))
      (SheafOfModules.unit _) ≅
    homSheaf X.sheaf (homSheaf X.sheaf N (SheafOfModules.unit _))
      (SheafOfModules.unit _) :=
  (homSheafFunctor X.sheaf (SheafOfModules.unit _)).mapIso
    (((homSheafFunctor X.sheaf (SheafOfModules.unit _)).mapIso e.op).op)

/-- The global double-dual model is the actual double-dual model on EACH
open affine chart. It is not an independently chosen local replacement. -/
def openPullbackEIso {A : CommRingCat.{0}} {V W : Scheme.{0}}
    (j : V ⟶ W) [IsOpenImmersion j] (p : W ⟶ Spec A) (M : ModuleCat A) :
    (pullback j).obj (E p M) ≅ E (j ≫ p) M := by
  let L := (pullback p).obj (tilde M)
  let D := homSheaf W.sheaf L (SheafOfModules.unit _)
  let F := homSheafFunctor V.sheaf (SheafOfModules.unit _)
  let e : (restrictFunctor j).obj (E p M) ≅
      homSheaf V.sheaf
        (homSheaf V.sheaf ((restrictFunctor j).obj L) (SheafOfModules.unit _))
        (SheafOfModules.unit _) :=
    dualSchemeRestrictionIso j D ≪≫
      (F.mapIso (dualSchemeRestrictionIso j L).op).symm
  exact ((restrictFunctorIsoPullback j).app (E p M)).symm ≪≫ e ≪≫
    doubleDualIso ((restrictFunctorIsoPullback j).app L ≪≫
      (pullbackComp j p).app (tilde M))

/-- The same comparison with a specified structural map on the chart. -/
def openPullbackEIsoOfComp {A : CommRingCat.{0}} {V W : Scheme.{0}}
    (j : V ⟶ W) [IsOpenImmersion j] (p : W ⟶ Spec A)
    (q : V ⟶ Spec A) (h : j ≫ p = q) (M : ModuleCat A) :
    (pullback j).obj (E p M) ≅ E q M :=
  openPullbackEIso j p M ≪≫
    doubleDualIso ((pullbackCongr h).app (tilde M))
end CoherentModelActual

end

end

end OAI
