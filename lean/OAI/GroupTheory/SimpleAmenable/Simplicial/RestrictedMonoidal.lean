import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.RestrictedNerve
import OAI.GroupTheory.SimpleAmenable.Simplicial.IntervalFunctor

namespace OAI

open CategoryTheory MonoidalCategory
namespace RestrictedNerve

section

section

variable {C : Type} [Groupoid.{0} C] (W : MorphismProperty C) [W.IsMultiplicative]
  [Fact W.StableUnderInverse]
noncomputable instance restricted_isIso {U V : WideSubcategory W} (f : U ⟶ V) : IsIso f := by
  refine ⟨⟨⟨inv f.hom,?_⟩,?_,?_⟩⟩
  · exact (Fact.out : W.StableUnderInverse) (asIso f.hom) f.property
  · apply WideSubcategory.hom_ext; exact IsIso.hom_inv_id f.hom
  · apply WideSubcategory.hom_ext; exact IsIso.inv_hom_id f.hom
noncomputable instance restricted_groupoid : Groupoid (WideSubcategory W) :=
  Groupoid.ofIsIso (fun _ => inferInstance)
instance strings_inverse (n : ℕ) : Fact (W.functorCategory (Fin (n+1))).StableUnderInverse where
  out _ _ e h i := by
    have hi := (Fact.out : W.StableUnderInverse) (e.app i) (h i)
    exact hi
noncomputable instance strings_isIso {n : ℕ} {U V : Strings W n} (f : U ⟶ V) : IsIso f := by
  let : IsIso f.hom := NatIso.isIso_of_isIso_app f.hom
  refine ⟨⟨⟨inv f.hom,?_⟩,?_,?_⟩⟩
  · intro i
    rw [NatIso.isIso_inv_app]
    exact (Fact.out : W.StableUnderInverse) (asIso (f.hom.app i)) (f.property i)
  · apply WideSubcategory.hom_ext; exact IsIso.hom_inv_id f.hom
  · apply WideSubcategory.hom_ext; exact IsIso.inv_hom_id f.hom
noncomputable instance strings_groupoid (n : ℕ) : Groupoid (Strings W n) :=
  Groupoid.ofIsIso (fun _ => inferInstance)
omit [Fact W.StableUnderInverse] in
@[simp] lemma wide_hom_inv {source target : WideSubcategory W} (iso : source ≅ target) :
    iso.hom.hom ≫ iso.inv.hom = 𝟙 _ := congrArg (fun arrow => arrow.hom) iso.hom_inv_id
omit [Fact W.StableUnderInverse] in
@[simp] lemma wide_inv_hom {source target : WideSubcategory W} (iso : source ≅ target) :
    iso.inv.hom ≫ iso.hom.hom = 𝟙 _ := congrArg (fun arrow => arrow.hom) iso.inv_hom_id
end

variable {C : Type} [Groupoid.{0} C] (W : MorphismProperty C)
  [Fact W.StableUnderInverse] [MonoidalCategory C] [SymmetricCategory C]
  [W.IsStableUnderBraiding]
instance strings_monoidal (n : ℕ) : (W.functorCategory (Fin (n+1))).IsMonoidalStable where
  whiskerLeft object _ _ arrow member index :=
    W.whiskerLeft_mem (object.obj index) (arrow.app index) (member index)
  whiskerRight arrow member object index :=
    W.whiskerRight_mem (arrow.app index) (member index) (object.obj index)
  associator_hom_mem first second third index :=
    W.associator_hom_mem (first.obj index) (second.obj index) (third.obj index)
  associator_inv_mem first second third index :=
    W.associator_inv_mem (first.obj index) (second.obj index) (third.obj index)
  leftUnitor_hom_mem object index := W.leftUnitor_hom_mem (object.obj index)
  leftUnitor_inv_mem object index := W.leftUnitor_inv_mem (object.obj index)
  rightUnitor_hom_mem object index := W.rightUnitor_hom_mem (object.obj index)
  rightUnitor_inv_mem object index := W.rightUnitor_inv_mem (object.obj index)
instance strings_braided (n : ℕ) : (W.functorCategory (Fin (n+1))).IsStableUnderBraiding where
  braiding_hom_mem first second index := W.braiding_hom_mem (first.obj index) (second.obj index)
  braiding_inv_mem first second index := W.braiding_inv_mem (first.obj index) (second.obj index)
noncomputable abbrev inclusion := wideSubcategoryInclusion W
noncomputable instance inclusionMonoidal : (inclusion W).Monoidal :=
  Functor.CoreMonoidal.toMonoidal {
    εIso := Iso.refl _
    μIso _ _ := Iso.refl _
    μIso_hom_natural_left := by intros; simp
    μIso_hom_natural_right := by intros; simp
    associativity := by intros; simp
    left_unitality := by intros; simp
    right_unitality := by intros; simp }
noncomputable instance inclusionBraided : (inclusion W).Braided where
  braided _ _ := by
    change 𝟙 _ ≫ (β_ _ _).hom = (β_ _ _).hom ≫ 𝟙 _
    simp
noncomputable instance reindexMonoidal {n m : ℕ} (u : Fin (n+1) ⥤ Fin (m+1)) :
    (reindex W u).Monoidal := Functor.CoreMonoidal.toMonoidal {
  εIso := Iso.refl _
  μIso _ _ := Iso.refl _
  μIso_hom_natural_left := by
    intro X Y f X'
    apply WideSubcategory.hom_ext
    ext i
    change (f.hom.app (u.obj i) ▷ X'.obj.obj (u.obj i)) ≫ 𝟙 _ =
      𝟙 _ ≫ (f.hom.app (u.obj i) ▷ X'.obj.obj (u.obj i))
    simp
  μIso_hom_natural_right := by
    intro X Y X' f
    apply WideSubcategory.hom_ext
    ext i
    change (X'.obj.obj (u.obj i) ◁ f.hom.app (u.obj i)) ≫ 𝟙 _ =
      𝟙 _ ≫ (X'.obj.obj (u.obj i) ◁ f.hom.app (u.obj i))
    simp
  associativity := by
    intro X Y Z
    apply WideSubcategory.hom_ext
    ext i
    let x := X.obj.obj (u.obj i)
    let y := Y.obj.obj (u.obj i)
    let z := Z.obj.obj (u.obj i)
    change (𝟙 (x ⊗ y) ▷ z) ≫ 𝟙 _ ≫ (α_ x y z).hom =
      (α_ x y z).hom ≫ (x ◁ 𝟙 (y ⊗ z)) ≫ 𝟙 _
    simp
  left_unitality := by
    intro X
    apply WideSubcategory.hom_ext
    ext i
    let x := X.obj.obj (u.obj i)
    change (λ_ x).hom = (𝟙 (𝟙_ C) ▷ x) ≫ 𝟙 _ ≫ (λ_ x).hom
    simp
  right_unitality := by
    intro X
    apply WideSubcategory.hom_ext
    ext i
    let x := X.obj.obj (u.obj i)
    change (ρ_ x).hom = (x ◁ 𝟙 (𝟙_ C)) ≫ 𝟙 _ ≫ (ρ_ x).hom
    simp }

noncomputable instance reindexBraided {n m : ℕ} (u : Fin (n+1) ⥤ Fin (m+1)) :
    (reindex W u).Braided where
  braided _ _ := by
    apply WideSubcategory.hom_ext; ext i
    change 𝟙 _ ≫ (β_ _ _).hom = (β_ _ _).hom ≫ 𝟙 _
    simp
end

open IntervalBar IntervalBar.Diagram

variable {C : Type} [Groupoid.{0} C] (W : MorphismProperty C)
  [Fact W.StableUnderInverse] [MonoidalCategory C] [SymmetricCategory C]
  [W.IsStableUnderBraiding]
variable (I : Type) [Preorder I]
noncomputable abbrev diagramInclusion := Diagram.map (I:=I) (inclusion W)
abbrev PosDiagrams := InducedCategory (Diagram C I) (diagramInclusion W I).obj
def diagramProperty : MorphismProperty (PosDiagrams W I) :=
  fun _ _ f => ∀ i j h, W (f.hom.app i j h)
instance diagramProperty_multiplicative : (diagramProperty W I).IsMultiplicative where
  id_mem object first last ordered := W.id_mem ((diagramInclusion W I).obj object |>.obj first last ordered)
  comp_mem first second hfirst hsecond start finish ordered :=
    W.comp_mem (first.hom.app start finish ordered) (second.hom.app start finish ordered)
      (hfirst start finish ordered) (hsecond start finish ordered)

variable {I}
noncomputable def stringVertex {n : ℕ} (A : Diagram (Strings W n) I) (t : Fin (n+1)) :
    PosDiagrams W I where
  obj i j h := ⟨(A.obj i j h).obj.obj t⟩
  unit i := {
    hom := ⟨(A.unit i).hom.hom.app t,(A.unit i).hom.property t⟩
    inv := ⟨(A.unit i).inv.hom.app t,(A.unit i).inv.property t⟩
    hom_inv_id := by
      apply WideSubcategory.hom_ext
      exact congrArg (fun f => f.hom.app t) (A.unit i).hom_inv_id
    inv_hom_id := by
      apply WideSubcategory.hom_ext
      exact congrArg (fun f => f.hom.app t) (A.unit i).inv_hom_id }
  cut i j k hij hjk := {
    hom := ⟨(A.cut i j k hij hjk).hom.hom.app t,(A.cut i j k hij hjk).hom.property t⟩
    inv := ⟨(A.cut i j k hij hjk).inv.hom.app t,(A.cut i j k hij hjk).inv.property t⟩
    hom_inv_id := by
      apply WideSubcategory.hom_ext
      exact congrArg (fun f => f.hom.app t) (A.cut i j k hij hjk).hom_inv_id
    inv_hom_id := by
      apply WideSubcategory.hom_ext
      exact congrArg (fun f => f.hom.app t) (A.cut i j k hij hjk).inv_hom_id }
  left_unit i j h := by
    apply WideSubcategory.hom_ext
    exact congrArg (fun f => f.hom.app t) (A.left_unit i j h)
  right_unit i j h := by
    apply WideSubcategory.hom_ext
    exact congrArg (fun f => f.hom.app t) (A.right_unit i j h)
  associativity i j k l hij hjk hkl := by
    apply WideSubcategory.hom_ext
    exact congrArg (fun f => f.hom.app t) (A.associativity i j k l hij hjk hkl)
noncomputable def stringVertexMap {n : ℕ} (A : Diagram (Strings W n) I)
    {t s : Fin (n+1)} (f : t ⟶ s) :
    stringVertex W A t ⟶ stringVertex W A s :=
  InducedCategory.homMk {
    app i j h := (A.obj i j h).obj.map f
    unit i := by
      change (A.obj i i le_rfl).obj.map f ≫ ((A.unit i).hom.hom.app s ≫ 𝟙 _) =
        (A.unit i).hom.hom.app t ≫ 𝟙 _
      simp
    cut i j k hij hjk := by
      change ((A.obj i j hij).obj.map f ⊗ₘ (A.obj j k hjk).obj.map f) ≫
          (𝟙 _ ≫ (A.cut i j k hij hjk).hom.hom.app s) =
        (𝟙 _ ≫ (A.cut i j k hij hjk).hom.hom.app t) ≫ (A.obj i k _).obj.map f
      erw [Category.id_comp, Category.id_comp]
      exact (A.cut i j k hij hjk).hom.hom.naturality f }
noncomputable def transposeDiagramObj {n : ℕ} (A : Diagram (Strings W n) I) :
    Strings (diagramProperty W I) n := ⟨{
  obj := stringVertex W A
  map := stringVertexMap W A
  map_id t := by
    apply InducedCategory.hom_ext; apply Hom.ext; intro i j h
    exact (A.obj i j h).obj.map_id t
  map_comp f g := by
    apply InducedCategory.hom_ext; apply Hom.ext; intro i j h
    exact (A.obj i j h).obj.map_comp f g }⟩
noncomputable def transposeDiagramHom {n : ℕ} {A B : Diagram (Strings W n) I} (f : A ⟶ B) :
    transposeDiagramObj W A ⟶ transposeDiagramObj W B := ⟨{
  app t := InducedCategory.homMk {
    app i j h := (f.app i j h).hom.app t
    unit i := by
      change (f.app i i le_rfl).hom.app t ≫ ((B.unit i).hom.hom.app t ≫ 𝟙 _) =
        (A.unit i).hom.hom.app t ≫ 𝟙 _
      simpa using congrArg (fun f => f.hom.app t) (f.unit i)
    cut i j k hij hjk := by
      change ((f.app i j hij).hom.app t ⊗ₘ (f.app j k hjk).hom.app t) ≫
          (𝟙 _ ≫ (B.cut i j k hij hjk).hom.hom.app t) =
        (𝟙 _ ≫ (A.cut i j k hij hjk).hom.hom.app t) ≫ (f.app i k _).hom.app t
      erw [Category.id_comp, Category.id_comp]
      exact congrArg (fun f => f.hom.app t) (f.cut i j k hij hjk) }
  naturality s t g := by
    apply InducedCategory.hom_ext; apply Hom.ext; intro i j h
    exact (f.app i j h).hom.naturality g },
    fun t i j h => (f.app i j h).property t⟩
noncomputable def transposeDiagram (n : ℕ) : Diagram (Strings W n) I ⥤ Strings (diagramProperty W I) n where
  obj := transposeDiagramObj W
  map := transposeDiagramHom W
  map_id A := by
    apply WideSubcategory.hom_ext; apply NatTrans.ext; funext t
    apply InducedCategory.hom_ext; apply Hom.ext; intros; rfl
  map_comp f g := by
    apply WideSubcategory.hom_ext; apply NatTrans.ext; funext t
    apply InducedCategory.hom_ext; apply Hom.ext; intros; rfl
noncomputable def untransposeDiagramObj {n : ℕ} (F : Strings (diagramProperty W I) n) :
    Diagram (Strings W n) I where
  obj i j h := ⟨{
    obj t := ((F.obj.obj t).obj i j h).obj
    map f := (F.obj.map f).hom.app i j h
    map_id t := congrArg (fun f => f.hom.app i j h) (F.obj.map_id t)
    map_comp f g := congrArg (fun f => f.hom.app i j h) (F.obj.map_comp f g) }⟩
  unit i := {
    hom := ⟨{
      app t := ((F.obj.obj t).unit i).hom.hom
      naturality t s f := by
        have he := (F.obj.map f).hom.unit i
        change (F.obj.map f).hom.app i i le_rfl ≫ (((F.obj.obj s).unit i).hom.hom ≫ 𝟙 _) =
          ((F.obj.obj t).unit i).hom.hom ≫ 𝟙 _ at he
        erw [Category.comp_id, Category.comp_id] at he
        change (F.obj.map f).hom.app i i le_rfl ≫ ((F.obj.obj s).unit i).hom.hom =
          ((F.obj.obj t).unit i).hom.hom ≫ 𝟙 _
        erw [Category.comp_id]
        exact he }, fun t => ((F.obj.obj t).unit i).hom.property⟩
    inv := ⟨{
      app t := ((F.obj.obj t).unit i).inv.hom
      naturality t s f := by
        have he := (F.obj.map f).hom.unit i
        change (F.obj.map f).hom.app i i le_rfl ≫ (((F.obj.obj s).unit i).hom.hom ≫ 𝟙 _) =
          ((F.obj.obj t).unit i).hom.hom ≫ 𝟙 _ at he
        erw [Category.comp_id, Category.comp_id] at he
        change 𝟙 _ ≫ ((F.obj.obj s).unit i).inv.hom =
          ((F.obj.obj t).unit i).inv.hom ≫ (F.obj.map f).hom.app i i le_rfl
        apply (cancel_mono ((F.obj.obj s).unit i).hom.hom).mp
        erw [Category.id_comp, wide_inv_hom, Category.assoc, he, wide_inv_hom] },
          fun t => ((F.obj.obj t).unit i).inv.property⟩
    hom_inv_id := by
      apply WideSubcategory.hom_ext; ext t
      exact congrArg (fun g => g.hom) ((F.obj.obj t).unit i).hom_inv_id
    inv_hom_id := by
      apply WideSubcategory.hom_ext; ext t
      exact congrArg (fun g => g.hom) ((F.obj.obj t).unit i).inv_hom_id }
  cut i j k hij hjk := {
    hom := ⟨{
      app t := ((F.obj.obj t).cut i j k hij hjk).hom.hom
      naturality t s f := by
        have he := (F.obj.map f).hom.cut i j k hij hjk
        change ((F.obj.map f).hom.app i j hij ⊗ₘ (F.obj.map f).hom.app j k hjk) ≫
          (𝟙 _ ≫ ((F.obj.obj s).cut i j k hij hjk).hom.hom) =
          (𝟙 _ ≫ ((F.obj.obj t).cut i j k hij hjk).hom.hom) ≫ (F.obj.map f).hom.app i k _ at he
        erw [Category.id_comp, Category.id_comp] at he
        exact he },fun t => ((F.obj.obj t).cut i j k hij hjk).hom.property⟩
    inv := ⟨{
      app t := ((F.obj.obj t).cut i j k hij hjk).inv.hom
      naturality t s f := by
        have he := (F.obj.map f).hom.cut i j k hij hjk
        change ((F.obj.map f).hom.app i j hij ⊗ₘ (F.obj.map f).hom.app j k hjk) ≫
          (𝟙 _ ≫ ((F.obj.obj s).cut i j k hij hjk).hom.hom) =
          (𝟙 _ ≫ ((F.obj.obj t).cut i j k hij hjk).hom.hom) ≫ (F.obj.map f).hom.app i k _ at he
        erw [Category.id_comp, Category.id_comp] at he
        change (F.obj.map f).hom.app i k _ ≫ ((F.obj.obj s).cut i j k hij hjk).inv.hom =
          ((F.obj.obj t).cut i j k hij hjk).inv.hom ≫
          ((F.obj.map f).hom.app i j hij ⊗ₘ (F.obj.map f).hom.app j k hjk)
        apply (cancel_epi ((F.obj.obj t).cut i j k hij hjk).hom.hom).mp
        repeat' erw [← Category.assoc]
        erw [wide_hom_inv, Category.id_comp]
        erw [←he,Category.assoc,wide_hom_inv]
        exact Category.comp_id _ },
          fun t => ((F.obj.obj t).cut i j k hij hjk).inv.property⟩
    hom_inv_id := by
      apply WideSubcategory.hom_ext; ext t
      exact congrArg (fun g => g.hom) ((F.obj.obj t).cut i j k hij hjk).hom_inv_id
    inv_hom_id := by
      apply WideSubcategory.hom_ext; ext t
      exact congrArg (fun g => g.hom) ((F.obj.obj t).cut i j k hij hjk).inv_hom_id }
  left_unit i j h := by
    apply WideSubcategory.hom_ext; ext t
    exact congrArg (fun g => g.hom) ((F.obj.obj t).left_unit i j h)
  right_unit i j h := by
    apply WideSubcategory.hom_ext; ext t
    exact congrArg (fun g => g.hom) ((F.obj.obj t).right_unit i j h)
  associativity i j k l hij hjk hkl := by
    apply WideSubcategory.hom_ext; ext t
    exact congrArg (fun g => g.hom) ((F.obj.obj t).associativity i j k l hij hjk hkl)
noncomputable def untransposeDiagramHom {n : ℕ} {A B : Strings (diagramProperty W I) n} (f : A ⟶ B) :
    untransposeDiagramObj W A ⟶ untransposeDiagramObj W B where
  app i j h := ⟨{
    app t := (f.hom.app t).hom.app i j h
    naturality t s g := congrArg (fun f => f.hom.app i j h) (f.hom.naturality g) },
      fun t => f.property t i j h⟩
  unit i := by
    apply WideSubcategory.hom_ext; ext t
    have he := (f.hom.app t).hom.unit i
    change (f.hom.app t).hom.app i i le_rfl ≫ (((B.obj.obj t).unit i).hom.hom ≫ 𝟙 _) =
      ((A.obj.obj t).unit i).hom.hom ≫ 𝟙 _ at he
    change (f.hom.app t).hom.app i i le_rfl ≫ ((B.obj.obj t).unit i).hom.hom =
      ((A.obj.obj t).unit i).hom.hom
    erw [Category.comp_id, Category.comp_id] at he
    exact he
  cut i j k hij hjk := by
    apply WideSubcategory.hom_ext; ext t
    have he := (f.hom.app t).hom.cut i j k hij hjk
    change ((f.hom.app t).hom.app i j hij ⊗ₘ (f.hom.app t).hom.app j k hjk) ≫
        (𝟙 _ ≫ ((B.obj.obj t).cut i j k hij hjk).hom.hom) =
      (𝟙 _ ≫ ((A.obj.obj t).cut i j k hij hjk).hom.hom) ≫ (f.hom.app t).hom.app i k _ at he
    change ((f.hom.app t).hom.app i j hij ⊗ₘ (f.hom.app t).hom.app j k hjk) ≫
      ((B.obj.obj t).cut i j k hij hjk).hom.hom =
      ((A.obj.obj t).cut i j k hij hjk).hom.hom ≫ (f.hom.app t).hom.app i k _
    erw [Category.id_comp, Category.id_comp] at he
    exact he
noncomputable def untransposeDiagram (n : ℕ) : Strings (diagramProperty W I) n ⥤ Diagram (Strings W n) I where
  obj := untransposeDiagramObj W
  map := untransposeDiagramHom W
  map_id A := by
    apply Hom.ext; intro i j h
    apply WideSubcategory.hom_ext; ext t; rfl
  map_comp f g := by
    apply Hom.ext; intro i j h
    apply WideSubcategory.hom_ext; ext t; rfl
noncomputable def diagramEquivalence (n : ℕ) : Diagram (Strings W n) I ≌ Strings (diagramProperty W I) n where
  functor := transposeDiagram W n
  inverse := untransposeDiagram W n
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  functor_unitIso_comp A := by
    change (transposeDiagram W n).map (𝟙 A) ≫ 𝟙 _ = 𝟙 _
    erw [Category.comp_id]
    exact (transposeDiagram W n).map_id A
noncomputable instance (n : ℕ) : (transposeDiagram (I:=I) W n).IsEquivalence :=
  (diagramEquivalence W n).isEquivalence_functor
end RestrictedNerve

end OAI
