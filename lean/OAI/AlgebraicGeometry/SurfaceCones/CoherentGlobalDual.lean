import Mathlib

namespace OAI

section

/-! Local linear Hom for sheaves of modules and coherence of duals on Noetherian schemes. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite

namespace CoherentDual
universe v u w z
variable {C : Type u} [Category.{v} C] (R : Cᵒᵖ ⥤ CommRingCat.{w})
  (M N : PresheafOfModules.{z} (R ⋙ forget₂ CommRingCat RingCat))

abbrev LocalAddHom (X : C) :=
  (Over.forget X).op ⋙ M.presheaf ⟶ (Over.forget X).op ⋙ N.presheaf

variable {R M N}

abbrev localApp {X : C} (f : LocalAddHom R M N X) (Y : (Over X)ᵒᵖ) :
    M.obj (op Y.unop.left) →+ N.obj (op Y.unop.left) := (f.app Y).hom

def localSMul {X : C} (r : R.obj (op X)) (f : LocalAddHom R M N X) :
    LocalAddHom R M N X where
  app Y := AddCommGrpCat.ofHom ((R.map Y.unop.hom.op r) • localApp f Y)
  naturality {Y Z} g := by
    ext x
    change (R.map Z.unop.hom.op r) • localApp f Z (M.map g.unop.left.op x) =
      N.map g.unop.left.op ((R.map Y.unop.hom.op r) • localApp f Y x)
    rw [N.map_smul]
    have hf := ConcreteCategory.congr_hom (f.naturality g) x
    change localApp f Z (M.map g.unop.left.op x) =
      N.map g.unop.left.op (localApp f Y x) at hf
    rw [hf]
    congr 1
    change R.map Z.unop.hom.op r = R.map g.unop.left.op (R.map Y.unop.hom.op r)
    rw [← Functor.map_comp_apply, ← op_comp, Over.w]

instance localHomSMul (X : C) : SMul (R.obj (op X)) (LocalAddHom R M N X) :=
  ⟨localSMul⟩

@[simp]
lemma local_smul_app {X : C} (r : R.obj (op X)) (f : LocalAddHom R M N X)
    (Y : (Over X)ᵒᵖ) (x : M.obj (op Y.unop.left)) :
    localApp (r • f) Y x = R.map Y.unop.hom.op r • localApp f Y x := rfl

@[simp]
lemma local_add_app {X : C} (f g : LocalAddHom R M N X)
    (Y : (Over X)ᵒᵖ) (x : M.obj (op Y.unop.left)) :
    localApp (f + g) Y x = localApp f Y x + localApp g Y x := rfl

@[simp]
lemma local_zero_app {X : C} (Y : (Over X)ᵒᵖ) (x : M.obj (op Y.unop.left)) :
    localApp (0 : LocalAddHom R M N X) Y x = 0 := rfl

lemma local_ext {X : C} {f g : LocalAddHom R M N X}
    (h : ∀ Y x, localApp f Y x = localApp g Y x) : f = g := by
  ext Y x
  exact h Y x

instance localHomModule (X : C) : Module (R.obj (op X)) (LocalAddHom R M N X) where
  one_smul f := by apply local_ext; intro Y x; simp
  mul_smul r s f := by apply local_ext; intro Y x; simp [mul_smul]
  smul_zero r := by apply local_ext; intro Y x; simp
  smul_add r f g := by apply local_ext; intro Y x; simp [smul_add]
  add_smul r s f := by apply local_ext; intro Y x; simp [add_smul]
  zero_smul f := by apply local_ext; intro Y x; simp

/-- Local morphisms that are linear for every local ring of sections. -/
def linearLocalHom (X : C) : Submodule (R.obj (op X)) (LocalAddHom R M N X) where
  carrier := {f | ∀ (Y : (Over X)ᵒᵖ) (r : R.obj (op Y.unop.left))
    (x : M.obj (op Y.unop.left)), localApp f Y (r • x) = r • localApp f Y x}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg Y r x
    simp only [local_add_app]
    rw [hf, hg, smul_add]
  smul_mem' := by
    intro r f hf Y s x
    simp only [local_smul_app]
    rw [hf, smul_comm]


/-- Linearity is preserved by restricting local natural transformations. -/
def linearLocalSubfunctor : Subfunctor (presheafHom M.presheaf N.presheaf) where
  obj X := (linearLocalHom (R := R) (M := M) (N := N) X.unop).carrier
  map {X Y} f α hα := by
    intro Z r x
    exact hα ((Over.map f.unop).op.obj Z) r x

/-- The linear internal Hom presheaf, with its natural module structure. -/
def homPresheaf : PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat) where
  obj X := ModuleCat.of (R.obj X) (linearLocalHom (R := R) (M := M) (N := N) X.unop)
  map {X Y} f := ModuleCat.ofHom
    (X := ModuleCat.of (R.obj X) (linearLocalHom (R := R) (M := M) (N := N) X.unop))
    (Y := (ModuleCat.restrictScalars (R.map f).hom).obj
      (ModuleCat.of (R.obj Y) (linearLocalHom (R := R) (M := M) (N := N) Y.unop)))
    { toFun α := ⟨(presheafHom M.presheaf N.presheaf).map f α.1,
        (linearLocalSubfunctor (R := R) (M := M) (N := N)).map f α.2⟩
      map_add' := by intro α β; rfl
      map_smul' := by
        intro r α
        apply Subtype.ext
        apply local_ext
        intro Z x
        change (R.map ((Over.map f.unop).obj Z.unop).hom.op r) •
          localApp α.1 ((Over.map f.unop).op.obj Z) x =
          R.map Z.unop.hom.op (R.map f r) •
          localApp α.1 ((Over.map f.unop).op.obj Z) x
        congr 1
        change R.map (Z.unop.hom ≫ f.unop).op r = _
        rw [op_comp, Functor.map_comp_apply]
        rfl }
  map_id X := by
    ext α
    apply Subtype.ext
    exact Functor.map_id_apply (presheafHom M.presheaf N.presheaf) X α.1
  map_comp f g := by
    ext α
    apply Subtype.ext
    exact Functor.map_comp_apply (presheafHom M.presheaf N.presheaf) f g α.1

lemma local_naturality {X : C} (f : LocalAddHom R M N X)
    {Y Z : Over X} (g : Z ⟶ Y) (x : M.obj (op Y.left)) :
    N.map g.left.op (localApp f (op Y) x) =
      localApp f (op Z) (M.map g.left.op x) := by
  exact (ConcreteCategory.congr_hom (f.naturality g.op) x).symm

/-- Pointwise local linearity is a sheaf-local condition. -/
theorem linearLocalSubfunctor_isSheaf {J : GrothendieckTopology C}
    (hN : Presheaf.IsSheaf J N.presheaf) :
    Presheaf.IsSheaf J (linearLocalSubfunctor (R := R) (M := M) (N := N)).toFunctor := by
  rw [isSheaf_iff_isSheaf_of_type]
  apply (Subfunctor.isSheaf_iff _
    ((isSheaf_iff_isSheaf_of_type _ _).1 (hN.hom M.presheaf))).2
  intro X f hf
  change LocalAddHom R M N X.unop at f
  change ∀ Y r x, localApp f Y (r • x) = r • localApp f Y x
  intro Y r x
  have hNt := Presheaf.isSheaf_comp_of_isSheaf J N.presheaf (forget AddCommGrpCat) hN
  have hsep := ((isSheaf_iff_isSheaf_of_type _ _).1 hNt
    _ (J.pullback_stable Y.unop.hom hf)).isSeparatedFor
  apply hsep.ext
  intro Z g hg
  change N.map g.op (localApp f Y (r • x)) =
    N.map g.op (r • localApp f Y x)
  rw [N.map_smul]
  let k : Over.mk (g ≫ Y.unop.hom) ⟶ Y.unop := Over.homMk g
  have hn (y : M.obj (op Y.unop.left)) :
      N.map g.op (localApp f Y y) =
        localApp f (op (Over.mk (g ≫ Y.unop.hom))) (M.map g.op y) :=
    local_naturality f k y
  rw [hn, hn]
  change localApp f (op (Over.mk (g ≫ Y.unop.hom))) (M.map g.op (r • x)) = _
  rw [M.map_smul]
  have hlin := hg (op (Over.mk (𝟙 Z))) (R.map g.op r) (M.map g.op x)
  change localApp f (op (Over.mk ((𝟙 Z) ≫ (g ≫ Y.unop.hom))))
      (R.map g.op r • M.map g.op x) =
    R.map g.op r • localApp f (op (Over.mk ((𝟙 Z) ≫ (g ≫ Y.unop.hom))))
      (M.map g.op x) at hlin
  erw [Category.id_comp] at hlin
  exact hlin

lemma homPresheaf_isSheaf {J : GrothendieckTopology C}
    (hN : Presheaf.IsSheaf J N.presheaf) :
    Presheaf.IsSheaf J (homPresheaf (R := R) (M := M) (N := N)).presheaf := by
  apply Presheaf.isSheaf_of_isSheaf_comp J _ (forget AddCommGrpCat)
  exact linearLocalSubfunctor_isSheaf hN

/-- The actual sheaf of modules of local linear maps. -/
def homSheaf {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{max u v w})
    (M N : SheafOfModules.{max u v w z}
      ((sheafCompose J (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})).obj R)) :
    SheafOfModules.{max u v w z}
      ((sheafCompose J (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})).obj R) where
  val := homPresheaf (R := R.obj) (M := M.val) (N := N.val)
  isSheaf := homPresheaf_isSheaf N.isSheaf


/-- Local linear transformations are exactly ordinary module morphisms on the
slice site. This identifies the just-constructed sheaf with genuine internal Hom. -/
def localHomEquiv (X : C) :
    linearLocalHom (R := R) (M := M) (N := N) X ≃
      ((PresheafOfModules.pushforward₀ (Over.forget X)
        (R ⋙ forget₂ CommRingCat RingCat)).obj M ⟶
       (PresheafOfModules.pushforward₀ (Over.forget X)
        (R ⋙ forget₂ CommRingCat RingCat)).obj N) where
  toFun f := PresheafOfModules.homMk f.val f.property
  invFun f := ⟨(PresheafOfModules.toPresheaf _).map f,
    fun Y r x => (f.app Y).hom.map_smul r x⟩
  left_inv f := by
    apply Subtype.ext
    apply local_ext
    intro Y x
    rfl
  right_inv f := by
    ext Y x
    rfl

/-- Sections of `homSheaf` are the actual morphisms of the restricted sheaves. -/
def homSheafSectionsEquiv {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{max u v w})
    (M N : SheafOfModules.{max u v w z}
      ((sheafCompose J (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})).obj R))
    (X : C) :
    (homSheaf R M N).val.obj (op X) ≃ (M.over X ⟶ N.over X) where
  toFun f := ⟨PresheafOfModules.homMk f.val f.property⟩
  invFun f := ⟨(PresheafOfModules.toPresheaf _).map f.val,
    fun Y r x => (f.val.app Y).hom.map_smul r x⟩
  left_inv f := by
    apply Subtype.ext
    apply local_ext
    intro Y x
    rfl
  right_inv f := by
    ext Y x
    rfl


section Unit
variable {C₀ : Type u} [Category.{u} C₀]
  {R₀ : C₀ᵒᵖ ⥤ CommRingCat.{u}}
  {N₀ : PresheafOfModules.{u} (R₀ ⋙ forget₂ CommRingCat RingCat)}

def unitLocalMap {X : C₀} (x : N₀.obj (op X)) :
    linearLocalHom (R := R₀) (M := PresheafOfModules.unit
      (R₀ ⋙ forget₂ CommRingCat RingCat)) (N := N₀) X := by
  refine ⟨{
    app := fun Y => AddCommGrpCat.ofHom ({
      toFun := fun (r : R₀.obj (op Y.unop.left)) => r • (N₀.map Y.unop.hom.op x : N₀.obj (op Y.unop.left))
      map_zero' := zero_smul _ _
      map_add' := fun r s => add_smul r s _ } :
      R₀.obj (op Y.unop.left) →+ N₀.obj (op Y.unop.left))
    naturality := ?_ }, ?_⟩
  · intro Y Z g
    ext r
    change R₀.obj (op Y.unop.left) at r
    change R₀.map g.unop.left.op r • N₀.map Z.unop.hom.op x =
      N₀.map g.unop.left.op (r • (N₀.map Y.unop.hom.op x : N₀.obj (op Y.unop.left)))
    erw [N₀.map_smul, ← N₀.map_comp_apply, ← op_comp, Over.w]
    rfl
  · intro Y r s
    change R₀.obj (op Y.unop.left) at s
    change (r * s) • N₀.map Y.unop.hom.op x =
      r • s • N₀.map Y.unop.hom.op x
    exact mul_smul r s _

/-- The expected free rank-one evaluation law, with the local ring action. -/
def unitLocalEquiv (X : C₀) :
    linearLocalHom (R := R₀) (M := PresheafOfModules.unit
      (R₀ ⋙ forget₂ CommRingCat RingCat)) (N := N₀) X ≃ₗ[R₀.obj (op X)]
      N₀.obj (op X) where
  toFun f := localApp f.val (op (Over.mk (𝟙 X))) (1 : R₀.obj (op X))
  invFun := unitLocalMap
  map_add' f g := rfl
  map_smul' r f := by
    change R₀.map (𝟙 X).op r • localApp f.val (op (Over.mk (𝟙 X))) (1 : R₀.obj (op X)) = _
    simp
  left_inv f := by
    apply Subtype.ext
    apply local_ext
    intro Y r
    change R₀.obj (op Y.unop.left) at r
    change r • N₀.map Y.unop.hom.op
      (localApp f.val (op (Over.mk (𝟙 X))) (1 : R₀.obj (op X))) = localApp f.val Y r
    let g : Y.unop ⟶ Over.mk (𝟙 X) := Over.homMk Y.unop.hom (by simp)
    have hn := local_naturality f.val g (1 : R₀.obj (op X))
    change N₀.map Y.unop.hom.op (localApp f.val (op (Over.mk (𝟙 X))) (1 : R₀.obj (op X))) =
      localApp f.val Y (R₀.map Y.unop.hom.op 1) at hn
    rw [map_one] at hn
    erw [hn, ← f.property Y r (1 : R₀.obj (op Y.unop.left))]
    exact congrArg (fun (a : R₀.obj (op Y.unop.left)) => localApp f.val Y a) (mul_one r)
  right_inv x := by
    dsimp [unitLocalMap, localApp]
    simp
    exact one_smul (R₀.obj (op X)) x

end Unit


end CoherentDual


namespace CoherentDual
section UnitIso
universe u
variable {C : Type u} [Category.{u} C]
  {R : Cᵒᵖ ⥤ CommRingCat.{u}}
  (N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))

/-- Evaluation at one is an isomorphism of module presheaves, not just a
bijection on global morphisms. -/
def unitHomPresheafIso :
    homPresheaf (R := R) (M := PresheafOfModules.unit
      (R ⋙ forget₂ CommRingCat RingCat)) (N := N) ≅ N :=
  PresheafOfModules.isoMk (fun X => (unitLocalEquiv (N₀ := N) X.unop).toModuleIso) (by
    intro X Y g
    ext f
    change localApp f.val (op (Over.mk ((𝟙 Y.unop) ≫ g.unop))) (1 : R.obj Y) =
      N.map g (localApp f.val (op (Over.mk (𝟙 X.unop))) (1 : R.obj X))
    erw [Category.id_comp]
    let a : Over.mk g.unop ⟶ Over.mk (𝟙 X.unop) := Over.homMk g.unop (by simp)
    have hn := local_naturality f.val a (1 : R.obj X)
    change N.map g (localApp f.val (op (Over.mk (𝟙 X.unop))) (1 : R.obj X)) =
      localApp f.val (op (Over.mk g.unop)) (R.map g 1) at hn
    have h1 : R.map g (1 : R.obj X) = (1 : R.obj Y) := (R.map g).hom.map_one
    rw [h1] at hn
    exact hn.symm)

variable {J : GrothendieckTopology C} (R₁ : Sheaf J CommRingCat.{u})
  (N₁ : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R₁))

/-- The genuine internal Hom from the structure sheaf is the target sheaf. -/
def unitHomSheafIso :
    homSheaf R₁ (SheafOfModules.unit _) N₁ ≅ N₁ :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso (unitHomPresheafIso N₁.val)

end UnitIso
end CoherentDual

namespace CoherentDual
section Functor
universe u
variable {C : Type u} [Category.{u} C]
  {R : Cᵒᵖ ⥤ CommRingCat.{u}}
  {M M' N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)}

/-- Precomposition in the genuine module of local linear maps. -/
def precompLocal (f : M ⟶ M') (X : C) :
    linearLocalHom (R := R) (M := M') (N := N) X →ₗ[R.obj (op X)]
      linearLocalHom (R := R) (M := M) (N := N) X where
  toFun h := ⟨Functor.whiskerLeft (Over.forget X).op
      ((PresheafOfModules.toPresheaf _).map f) ≫ h.val, by
    intro Y r x
    change localApp h.val Y (f.app (op Y.unop.left) (r • x)) =
      r • localApp h.val Y (f.app (op Y.unop.left) x)
    rw [(f.app _).hom.map_smul, h.property]⟩
  map_add' h k := by
    apply Subtype.ext
    apply local_ext
    intro Y x
    rfl
  map_smul' r h := by
    apply Subtype.ext
    apply local_ext
    intro Y x
    rfl

def precompPresheaf (f : M ⟶ M') :
    homPresheaf (R := R) (M := M') (N := N) ⟶
      homPresheaf (R := R) (M := M) (N := N) where
  app X := ModuleCat.ofHom (precompLocal f X.unop)
  naturality g := by
    ext h
    apply Subtype.ext
    apply local_ext
    intro Y x
    rfl

variable {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u})
variable (N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))

/-- Contravariant internal Hom into a fixed sheaf. -/
def homSheafFunctor : (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))ᵒᵖ ⥤ SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) where
  obj M := homSheaf.{u,u,u,u} R M.unop N
  map {M M'} f := by
    constructor
    change homPresheaf (R := R.obj) (M := M.unop.val) (N := N.val) ⟶
      homPresheaf (R := R.obj) (M := M'.unop.val) (N := N.val)
    exact precompPresheaf (R := R.obj) (M := M'.unop.val)
      (M' := M.unop.val) (N := N.val) f.unop.val
  map_id M := by
    ext X h
    apply Subtype.ext
    apply local_ext
    intro Y x
    rfl
  map_comp f g := by
    ext X h
    apply Subtype.ext
    apply local_ext
    intro Y x
    rfl

/-- Evaluation of internal Hom is the actual representable functor on the
slice site. In particular no local presentation or exactness is postulated. -/
def homSheafEvaluationIso (X : C) :
    homSheafFunctor R N ⋙ SheafOfModules.forget _ ⋙
        PresheafOfModules.evaluation _ (op X) ⋙ forget _ ≅
      (SheafOfModules.overFunctor.{u,u,u,u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) X).op ⋙ yoneda.obj (N.over X) :=
  NatIso.ofComponents
    (fun M => Equiv.toIso (homSheafSectionsEquiv R M.unop N X)) (by
      intro M M' f
      ext h
      rfl)

variable [HasBinaryProducts C]

instance homSheafEvaluation_preservesLimits (X : C) :
    PreservesLimitsOfSize.{u,u} (homSheafFunctor R N ⋙ SheafOfModules.forget _ ⋙
        PresheafOfModules.evaluation _ (op X) ⋙ forget _) :=
  by
    have : PreservesColimitsOfSize.{u,u}
        (SheafOfModules.overFunctor.{u,u,u,u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) X) :=
      (SheafOfModules.overPushforwardOverAdj.{u,u,u,u} X).leftAdjoint_preservesColimits
    have : PreservesLimitsOfSize.{u,u}
        (SheafOfModules.overFunctor.{u,u,u,u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) X).op :=
      preservesLimitsOfSize_op _
    exact preservesLimits_of_natIso (homSheafEvaluationIso R N X).symm

instance homSheafModuleEvaluation_preservesLimits (X : C) :
    PreservesLimitsOfSize.{u,u} (homSheafFunctor R N ⋙ SheafOfModules.forget _ ⋙
        PresheafOfModules.evaluation _ (op X)) :=
  by
    have : PreservesLimitsOfSize.{u,u} ((homSheafFunctor R N ⋙ SheafOfModules.forget _ ⋙
        PresheafOfModules.evaluation _ (op X)) ⋙ forget _) :=
      homSheafEvaluation_preservesLimits R N X
    exact preservesLimits_of_reflects_of_preserves _ (forget _)

/-- Local linear Hom is left exact, because morphisms out of colimits turn
into limits after restriction to every slice site. -/
instance homSheafFunctor_preservesLimits :
    PreservesLimitsOfSize.{u,u} (homSheafFunctor R N) where
  preservesLimitsOfShape {D} _ := {
    preservesLimit := fun {K} => {
      preserves := fun {c} hc => ⟨by
        apply isLimitOfReflects (SheafOfModules.forget _)
        apply PresheafOfModules.evaluationJointlyReflectsLimits
        intro X
        have := homSheafModuleEvaluation_preservesLimits R N X.unop
        exact isLimitOfPreserves (homSheafFunctor R N ⋙ SheafOfModules.forget _ ⋙
          PresheafOfModules.evaluation _ X) hc⟩ } }

end Functor
end CoherentDual

namespace CoherentDual
section Exact
universe u
variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
  (N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))

instance homSheafFunctor_additive : (homSheafFunctor R N).Additive where
  map_add {M M'} f g := by
    ext X h
    apply Subtype.ext
    apply local_ext
    intro Y x
    change localApp h.val Y
        (f.unop.val.app (op Y.unop.left) x + g.unop.val.app (op Y.unop.left) x) =
      localApp h.val Y (f.unop.val.app (op Y.unop.left) x) +
        localApp h.val Y (g.unop.val.app (op Y.unop.left) x)
    exact map_add _ _ _

variable [HasBinaryProducts C]
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {M M' : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}

/-- Dualizing a genuine presentation gives the actual kernel. This is the
kernel description used to prove coherence of the model dual, not a
postulated exactness property of an abstract replacement dual. -/
def homCokernelIso (f : M ⟶ M') :
    homSheaf R (cokernel f) N ≅ kernel ((homSheafFunctor R N).map f.op) :=
  IsLimit.conePointUniqueUpToIso
    (KernelFork.mapIsLimit _
      (CokernelCofork.IsColimit.ofπOp (cokernel.π f) (cokernel.condition f)
        (cokernelIsCokernel f)) (homSheafFunctor R N))
    (limit.isLimit _)

end Exact
end CoherentDual

namespace CoherentDual
section FiniteFree
universe u
variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
  [HasBinaryProducts C]
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
  (I : Type u)

/-- The genuine internal Hom out of a free sheaf is the product of the target
sheaf, with no presentation/exactness assumed. -/
def homFreeIso : homSheaf R (SheafOfModules.free I) N ≅ ∏ᶜ (fun (_ : I) => N) :=
  (homSheafFunctor R N).mapIso
    (opCoproductIsoProduct (fun (_ : I) => SheafOfModules.unit _)) ≪≫
  PreservesProduct.iso (homSheafFunctor R N) _ ≪≫
  Pi.mapIso (fun (_ : I) => unitHomSheafIso R N)

variable [Finite I]

/-- The dual of a finite free sheaf really is the same finite free sheaf. -/
def dualFiniteFreeIso :
    homSheaf R (SheafOfModules.free I) (SheafOfModules.unit _) ≅
      SheafOfModules.free I := by
  have : HasFiniteBiproducts (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :=
    .of_hasFiniteProducts
  exact homFreeIso R (SheafOfModules.unit _) I ≪≫
  (biproduct.isoProduct (fun (_ : I) => SheafOfModules.unit _)).symm ≪≫
  biproduct.isoCoproduct _

end FiniteFree
end CoherentDual

open AlgebraicGeometry
namespace CoherentDual
section KernelConjugate
variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasKernels C]
  {A B A' B' : C}
/-- Transport a kernel through isomorphisms of its source and target. -/
def kernelConjugateIso (f : A ⟶ B) (eA : A ≅ A') (eB : B ≅ B') :
    kernel f ≅ kernel (eA.inv ≫ f ≫ eB.hom) :=
  kernel.mapIso _ _ eA eB (by simp)
end KernelConjugate

end CoherentDual

namespace CoherentLocality
universe u
section Map
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {M : SheafOfModules.{u} R} (P : M.Presentation)
  (F : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S)
  [PreservesColimitsOfSize.{u,u} F] (e : SheafOfModules.unit S ≅ F.obj (SheafOfModules.unit R))

instance presentationMap_finite [P.IsFinite] : (P.map F e).IsFinite := by
  constructor
  · constructor
    change Finite P.generators.I
    infer_instance
  · constructor
    change Finite P.relations.I
    infer_instance
end Map

section Local
variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

lemma finitePresentation_of_presentation [HasBinaryProducts C]
    {M : SheafOfModules.{u} R} (P : M.Presentation) [P.IsFinite] :
    M.IsFinitePresentation := by
  refine ⟨P.quasicoherentData, ?_⟩
  constructor
  intro X
  constructor
  · constructor
    change Finite P.generators.I
    infer_instance
  · constructor
    change Finite P.relations.I
    infer_instance

variable [∀ X Y, HasSheafify ((J.over X).over Y) AddCommGrpCat.{u}]
  [∀ X Y, ((J.over X).over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]

instance bind_finite (M : SheafOfModules.{u} R) {I : Type u}
    (X : I → C) (hX : J.CoversTop X)
    (D : ∀ i, (M.over (X i)).QuasicoherentData)
    [∀ i, (D i).IsFinitePresentation] :
    (SheafOfModules.QuasicoherentData.bind M X hX D).IsFinitePresentation := by
  constructor
  intro i
  constructor
  · constructor
    change Finite ((D i.1).presentation i.2).generators.I
    infer_instance
  · constructor
    change Finite ((D i.1).presentation i.2).relations.I
    infer_instance

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
lemma finitePresentation_of_coversTop (M : SheafOfModules.{u} R) {I : Type u}
    (X : I → C) (hX : J.CoversTop X)
    [∀ i, (M.over (X i)).IsFinitePresentation] : M.IsFinitePresentation := by
  choose D hD using fun i => SheafOfModules.IsFinitePresentation.exists_quasicoherentData
    (M.over (X i))
  let (i : I) : (D i).IsFinitePresentation := hD i
  exact ⟨SheafOfModules.QuasicoherentData.bind M X hX D, inferInstance⟩
end Local
end CoherentLocality
namespace CoherentRestriction
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]

instance preservesMonomorphisms : (Scheme.Modules.restrictFunctor f).PreservesMonomorphisms where
  preserves g hg := by
    let := hg
    have : Mono ((Scheme.Modules.toPresheafOfModules Y).map g) := inferInstance
    have hm : Mono ((Scheme.Modules.toPresheafOfModules X).map
        ((Scheme.Modules.restrictFunctor f).map g)) := by
      apply PresheafOfModules.mono_of_injective
      intro U
      exact PresheafOfModules.injective_of_mono
        ((Scheme.Modules.toPresheafOfModules Y).map g) (Opposite.op (f ''ᵁ U.unop))
    exact (Scheme.Modules.toPresheafOfModules X).mono_of_mono_map hm

instance additive : (Scheme.Modules.restrictFunctor f).Additive := by
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts
    (Scheme.Modules.restrictFunctor f)
  exact Functor.additive_of_preservesBinaryBiproducts _

instance preservesHomology : (Scheme.Modules.restrictFunctor f).PreservesHomology :=
  Functor.preservesHomology_of_preservesMonos_and_cokernels _

instance preservesFiniteLimits : PreservesFiniteLimits (Scheme.Modules.restrictFunctor f) :=
  (Scheme.Modules.restrictFunctor f).preservesFiniteLimits_of_preservesHomology
end CoherentRestriction

namespace CoherentExactAffine
universe u
variable {R : CommRingCat.{u}} {M N : ModuleCat.{u} R}

lemma localizations_comap_eq_map (f : M ⟶ N) (x : PrimeSpectrum.Top R) :
    ⇑(StructureSheaf.Localizations.comapFun f.hom x) =
      ⇑(LocalizedModule.map x.asIdeal.primeCompl f.hom) := by
  apply funext
  intro a
  induction a using LocalizedModule.induction_on with
  | h m s =>
    change StructureSheaf.Localizations.comapFun f.hom x (LocalizedModule.mk m s) =
      LocalizedModule.map x.asIdeal.primeCompl f.hom (LocalizedModule.mk m s)
    erw [LocalizedModule.map_mk]

lemma comap_injective (f : M ⟶ N) (hf : Function.Injective f) (U : (Spec R).Opens) :
    Function.Injective (StructureSheaf.comapₗ f.hom U U Set.Subset.rfl) := by
  intro a b hab
  apply Subtype.ext
  funext x
  apply LocalizedModule.map_injective x.1.asIdeal.primeCompl f.hom hf
  have h := congrArg (fun z => z.1 x) hab
  change StructureSheaf.Localizations.comapFun f.hom x.1 (a.1 x) =
    StructureSheaf.Localizations.comapFun f.hom x.1 (b.1 x) at h
  simpa only [localizations_comap_eq_map] using h

lemma tilde_map_app_injective (f : M ⟶ N) (hf : Function.Injective f)
    (U : (Spec R).Opens) :
    Function.Injective ((tilde.map f).val.app (.op U)) := by
  exact comap_injective f hf U

instance preservesMonomorphisms : (tilde.functor R).PreservesMonomorphisms where
  preserves f hf := by
    have hm : Mono ((SheafOfModules.forget _).map (tilde.map f)) :=
      PresheafOfModules.mono_of_injective fun {U} =>
        tilde_map_app_injective f ((ModuleCat.mono_iff_injective f).mp hf) U.unop
    change Mono (tilde.map f)
    exact (SheafOfModules.forget _).mono_of_mono_map hm

instance preservesHomology : (tilde.functor R).PreservesHomology :=
  Functor.preservesHomology_of_preservesMonos_and_cokernels _

instance preservesFiniteLimits : PreservesFiniteLimits (tilde.functor R) :=
  (tilde.functor R).preservesFiniteLimits_of_preservesHomology

end CoherentExactAffine
namespace CoherentGlobal
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/-- A finite module on a Noetherian affine has a finite *global*
presentation of its associated sheaf. -/
lemma exists_presentation_tilde {A : CommRingCat} [IsNoetherianRing A]
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

lemma exists_presentation_kernel_tilde {A : CommRingCat} [IsNoetherianRing A]
    {M N : ModuleCat A} [Module.Finite A M] (f : M ⟶ N) :
    ∃ P : (kernel (tilde.map f)).Presentation, P.IsFinite := by
  let e : kernel (tilde.map f) ≅ tilde (ModuleCat.of A f.hom.ker) :=
    (PreservesKernel.iso (tilde.functor A) f).symm ≪≫
      (tilde.functor A).mapIso (ModuleCat.kernelIsoKer f)
  obtain ⟨P, hP⟩ := exists_presentation_tilde (ModuleCat.of A f.hom.ker)
  let : P.IsFinite := hP
  refine ⟨@SheafOfModules.Presentation.ofIsIso _ _ _ _ _ _ _ _ e.inv e.isIso_inv P, ?_⟩
  constructor
  · constructor
    change Finite P.generators.I
    exact hP.isFiniteType_generators.finite
  · constructor
    change Finite P.relations.I
    exact hP.isFiniteType_relations.finite

lemma exists_presentation_kernel {A : CommRingCat} [IsNoetherianRing A]
    {M N : ModuleCat A} [Module.Finite A M] (f : tilde M ⟶ tilde N) :
    ∃ P : (kernel f).Presentation, P.IsFinite := by
  let g := (tilde.functor A).preimage f
  have hfg : (tilde.functor A).map g = f := (tilde.functor A).map_preimage f
  rw [← hfg]
  exact exists_presentation_kernel_tilde g

/-- On a Noetherian affine, an actual kernel between finite free sheaves
has a global finite presentation. This supplies the local input for duals. -/
lemma exists_presentation_kernel_free {A : CommRingCat} [IsNoetherianRing A]
    {I J : Type} [Finite I] [Finite J]
    (f : SheafOfModules.free (R := (Spec A).ringCatSheaf) I ⟶ SheafOfModules.free J) :
    ∃ P : (kernel f).Presentation, P.IsFinite := by
  let eI := (tildeFinsupp (R := A) I).symm
  let eJ := (tildeFinsupp (R := A) J).symm
  let g := eI.inv ≫ f ≫ eJ.hom
  let e := CoherentDual.kernelConjugateIso f eI eJ
  obtain ⟨P, hP⟩ := exists_presentation_kernel g
  let : P.IsFinite := hP
  refine ⟨P.ofIsIso e.inv, ?_⟩
  constructor
  · constructor
    change Finite P.generators.I
    exact hP.isFiniteType_generators.finite
  · constructor
    change Finite P.relations.I
    exact hP.isFiniteType_relations.finite

end CoherentGlobal


namespace CoherentGlobal
open Scheme.Modules

lemma exists_presentation_iso {C : Type} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat} [HasSheafify J AddCommGrpCat]
    [J.WEqualsLocallyBijective AddCommGrpCat] {M N : SheafOfModules R}
    (e : M ≅ N) (hp : ∃ P : M.Presentation, P.IsFinite) :
    ∃ P : N.Presentation, P.IsFinite := by
  obtain ⟨P, hP⟩ := hp
  let : P.IsFinite := hP
  refine ⟨P.ofIsIso e.hom, ?_⟩
  constructor
  · constructor
    change Finite P.generators.I
    infer_instance
  · constructor
    change Finite P.relations.I
    infer_instance

lemma exists_presentation_kernel_restrict {X : Scheme} [IsLocallyNoetherian X]
    {I J : Type} [Finite I] [Finite J]
    (f : SheafOfModules.free (R := X.ringCatSheaf) I ⟶ SheafOfModules.free J)
    (U : X.affineOpens) :
    ∃ P : ((restrictFunctor (U.2.isoSpec.inv ≫ U.1.ι)).obj (kernel f)).Presentation,
      P.IsFinite := by
  let h := U.2.isoSpec.inv ≫ U.1.ι
  let F : SheafOfModules X.ringCatSheaf ⥤
      SheafOfModules (Spec Γ(X, U.1)).ringCatSheaf := restrictFunctor h
  have : F.IsLeftAdjoint := inferInstanceAs (restrictFunctor h).IsLeftAdjoint
  have : PreservesFiniteLimits F := CoherentRestriction.preservesFiniteLimits h
  let eI := (SheafOfModules.mapFreeIso F I (restrictUnitIso h).symm).symm
  let eJ := (SheafOfModules.mapFreeIso F J (restrictUnitIso h).symm).symm
  let g := eI.inv ≫ F.map f ≫ eJ.hom
  let e : F.obj (kernel f) ≅ kernel g :=
    (PreservesKernel.iso F f) ≪≫ CoherentDual.kernelConjugateIso (F.map f) eI eJ
  have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  exact exists_presentation_iso e.symm (exists_presentation_kernel_free g)

lemma exists_presentation_affine_over
    {X : Scheme} (M : X.Modules) (U : X.affineOpens)
    (hp : ∃ P : ((restrictFunctor (U.2.isoSpec.inv ≫ U.1.ι)).obj M).Presentation,
      P.IsFinite) :
    ∃ P : (M.over U.1).Presentation, P.IsFinite := by
  let h := U.2.isoSpec.inv ≫ U.1.ι
  let F := restrictFunctor h
  let G : SheafOfModules (Spec Γ(X, U.1)).ringCatSheaf ⥤
      SheafOfModules (X.ringCatSheaf.over U.1) :=
    restrictFunctor U.2.isoSpec.hom ⋙ (overEquiv U.1).inverse
  have : G.IsLeftAdjoint := inferInstanceAs
    (restrictFunctor U.2.isoSpec.hom ⋙ (overEquiv U.1).inverse).IsLeftAdjoint
  let e : SheafOfModules.unit (X.ringCatSheaf.over U.1) ≅
      G.obj (SheafOfModules.unit (Spec Γ(X, U.1)).ringCatSheaf) :=
    (TopologicalSpace.Opens.sheafOfModulesEquivOverInverseUnit U.1 X.ringCatSheaf).symm ≪≫
      (overEquiv U.1).inverse.mapIso (restrictUnitIso U.2.isoSpec.hom).symm
  let q : (restrictFunctor U.2.isoSpec.hom).obj (F.obj M) ≅ M.restrict U.1.ι :=
    ((restrictFunctorComp U.2.isoSpec.hom h).app M).symm ≪≫
      (restrictFunctorCongr (by dsimp [h]; simp)).app M
  let j : G.obj (F.obj M) ≅ M.over U.1 :=
    (overEquiv U.1).inverse.mapIso q ≪≫
      (overEquiv U.1).inverse.mapIso ((overFunctorEquiv U.1).app M).symm ≪≫
      ((overEquiv U.1).unitIso.app (M.over U.1)).symm
  obtain ⟨P, hP⟩ := hp
  let := hP
  apply exists_presentation_iso j
  refine ⟨P.map G e, ?_⟩
  constructor
  · constructor
    change Finite P.generators.I
    exact hP.isFiniteType_generators.finite
  · constructor
    change Finite P.relations.I
    exact hP.isFiniteType_relations.finite

/-- An actual kernel of a map between finite free sheaves on a locally
Noetherian scheme is a finite-presentation sheaf. -/
lemma coherent_kernel_free {X : Scheme} [IsLocallyNoetherian X]
    {I J : Type} [Finite I] [Finite J]
    (f : SheafOfModules.free (R := X.ringCatSheaf) I ⟶ SheafOfModules.free J) :
    (kernel f).IsFinitePresentation := by
  have (U : X.affineOpens) : ((kernel f).over U.1).IsFinitePresentation := by
    obtain ⟨P, hP⟩ := exists_presentation_affine_over (kernel f) U
      (exists_presentation_kernel_restrict f U)
    apply +allowSynthFailures CoherentLocality.finitePresentation_of_presentation P
  exact CoherentLocality.finitePresentation_of_coversTop (kernel f)
    (fun U : X.affineOpens => U.1)
    ((Opens.coversTop_iff X _).mpr (iSup_affineOpens_eq_top X))
end CoherentGlobal


namespace CoherentLocality
section Pushforward
universe u
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X, HasSheafify (K.over X) AddCommGrpCat.{u}]
  [∀ X, (K.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  (G : D ⥤ C) [G.IsContinuous K J] [G.IsCocontinuous K J]
  (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{u} K J).obj R)
  (η : (SheafOfModules.pushforward φ).obj (SheafOfModules.unit R) ≅ SheafOfModules.unit S)
  [∀ X, (Over.post G).IsContinuous (K.over X) (J.over _)]

include η in
lemma finitePresentation_pushforward
    (h : ∀ (X : D) (Y : C) (f : G.obj X ⟶ Y),
      PreservesColimitsOfSize.{u, u} <|
      SheafOfModules.pushforward.{u} (R := (R.over Y)) (F := Over.post (X := X) G ⋙ Over.map f)
        (((Over.forget X).sheafPushforwardContinuous RingCat.{u} (K.over X) K).map φ))
    {M : SheafOfModules.{u} R} [M.IsFinitePresentation] :
    ((SheafOfModules.pushforward φ).obj M).IsFinitePresentation := by
  obtain ⟨P, hP⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData M
  refine ⟨P.pushforward G φ η h, ?_⟩
  constructor
  intro i
  constructor
  · constructor
    change Finite (P.presentation i.2.1).generators.I
    infer_instance
  · constructor
    change Finite (P.presentation i.2.1).relations.I
    infer_instance

include η in
lemma finitePresentation_pushforward_of_isLeftAdjoint
    [G.IsLeftAdjoint] [IsIso φ] [HasPullbacks C] [HasPullbacks D]
    {M : SheafOfModules.{u} R} [M.IsFinitePresentation] :
    ((SheafOfModules.pushforward φ).obj M).IsFinitePresentation := by
  apply +allowSynthFailures finitePresentation_pushforward G φ η _
  intro X Y f
  let G' := Over.post (X := X) G ⋙ Over.map f
  have : G'.IsContinuous (K.over X) (J.over Y) := Functor.isContinuous_comp _ _ _ (J.over _) _
  have : G'.IsCocontinuous (K.over X) (J.over Y) := isCocontinuous_comp _ _ _ (J.over _)
  let a : S.over X ⟶
      (G'.sheafPushforwardContinuous RingCat.{u} (K.over X) (J.over Y)).obj (R.over Y) :=
    ((Over.forget X).sheafPushforwardContinuous RingCat.{u} (K.over X) K).map φ
  let : IsIso a := inferInstanceAs (IsIso
    (((Over.forget X).sheafPushforwardContinuous RingCat.{u} (K.over X) K).map φ))
  have : (SheafOfModules.pushforward.{u} a).IsLeftAdjoint :=
    SheafOfModules.isLeftAdjoint_pushforward_of_isIso a
  infer_instance
end Pushforward
end CoherentLocality


namespace CoherentDual
section Global
variable {X : Scheme} [IsLocallyNoetherian X]
    (M : X.Modules) (P : M.Presentation) [P.IsFinite]
include P

/-- The actual structure-sheaf dual of a globally finitely presented sheaf
on a locally Noetherian scheme is coherent. -/
lemma coherent_dual_of_global_presentation :
    (homSheaf X.sheaf M (SheafOfModules.unit _)).IsFinitePresentation := by
  change SheafOfModules X.ringCatSheaf at M
  let : Finite P.generators.I :=
    (SheafOfModules.Presentation.IsFinite.isFiniteType_generators (p := P)).finite
  let : Finite P.relations.I :=
    (SheafOfModules.Presentation.IsFinite.isFiniteType_relations (p := P)).finite
  let N := SheafOfModules.unit X.ringCatSheaf
  let F := homSheafFunctor X.sheaf N
  let : F.Additive := homSheafFunctor_additive X.sheaf N
  let : PreservesLimitsOfSize.{0, 0} F := homSheafFunctor_preservesLimits X.sheaf N
  let f : SheafOfModules.free (R := X.ringCatSheaf) P.relations.I ⟶
      SheafOfModules.free (R := X.ringCatSheaf) P.generators.I :=
    P.relations.π ≫ kernel.ι P.generators.π
  have hf : f ≫ P.generators.π =
      (0 : SheafOfModules.free (R := X.ringCatSheaf) P.relations.I ⟶
        (M : SheafOfModules X.ringCatSheaf)) := by simp [f]
  let h := CokernelCofork.IsColimit.ofπOp P.generators.π hf P.isColimit
  let e : homSheaf X.sheaf M N ≅ kernel (F.map f.op) :=
    IsLimit.conePointUniqueUpToIso (KernelFork.mapIsLimit _ h F) (limit.isLimit _)
  let eG := dualFiniteFreeIso X.sheaf P.generators.I
  let eR := dualFiniteFreeIso X.sheaf P.relations.I
  let g := eG.inv ≫ F.map f.op ≫ eR.hom
  let ek : kernel (F.map f.op) ≅ kernel g :=
    kernelConjugateIso (F.map f.op) eG eR
  apply (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso
    (e ≪≫ ek).symm
  exact CoherentGlobal.coherent_kernel_free g
end Global
end CoherentDual

namespace CoherentGlobal
universe u
open Scheme.Modules
lemma opensDense {T : Type*} [TopologicalSpace T] (U : TopologicalSpace.Opens T) :
    U.overEquivalence.functor.IsDenseSubsite
      ((Opens.grothendieckTopology T).over U) (Opens.grothendieckTopology U) := by
  infer_instance
lemma opensPreservesHypercovers {T : Type*} [TopologicalSpace T] (U : TopologicalSpace.Opens T) :
    U.overEquivalence.functor.PreservesOneHypercovers
      ((Opens.grothendieckTopology T).over U) (Opens.grothendieckTopology U) := by
  exact Functor.PreservesOneHypercovers.of_coverPreserving
      (Functor.IsDenseSubsite.coverPreserving
        ((Opens.grothendieckTopology T).over U)
        (Opens.grothendieckTopology U) U.overEquivalence.functor)
lemma opensOverPostContinuous {T : Type u} [TopologicalSpace T] (U : TopologicalSpace.Opens T) :
    ∀ V : Over U, (Over.post U.overEquivalence.functor).IsContinuous
      (((Opens.grothendieckTopology T).over U).over V)
      ((Opens.grothendieckTopology U).over (U.overEquivalence.functor.obj V)) := by
  intro V
  apply Functor.isContinuous_iff_coverPreserving.mpr
  exact (Functor.IsDenseSubsite.coverPreserving
    ((Opens.grothendieckTopology T).over U)
    (Opens.grothendieckTopology U) U.overEquivalence.functor).overPost V

lemma finitePresentation_overEquiv_inverse {X : Scheme} (U : X.Opens)
    (M : U.toScheme.Modules) [M.IsFinitePresentation] :
    ((overEquiv U).inverse.obj M).IsFinitePresentation := by
  let := opensOverPostContinuous U
  exact @CoherentLocality.finitePresentation_pushforward_of_isLeftAdjoint
    _ _ _ _ _ _ _ _ _ _ _ _
    U.overEquivalence.functor
    _ _
    ((U.sheafRestrictSheafEquivOver.app X.ringCatSheaf).inv)
    (TopologicalSpace.Opens.sheafOfModulesEquivOverInverseUnit U X.ringCatSheaf)
    _ _ (U.sheafRestrictSheafEquivOver.app X.ringCatSheaf).isIso_inv _ _ M (by assumption)
end CoherentGlobal

end

end

end OAI
