import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.DiagonalComparison

namespace OAI

open CategoryTheory SimplicialObject Simplicial Opposite
namespace RestrictedNerve

variable {C : Type} [Groupoid.{0} C] (W : MorphismProperty C) [W.IsMultiplicative]
instance (n : ℕ) : (W.functorCategory (Fin (n+1))).IsMultiplicative where
  id_mem object index := W.id_mem (object.obj index)
  comp_mem first second hfirst hsecond index :=
    W.comp_mem (first.app index) (second.app index) (hfirst index) (hsecond index)
abbrev Strings (n : ℕ) := WideSubcategory (W.functorCategory (Fin (n+1)))
def allowed (n : ℕ) : ObjectProperty (Fin (n+1) ⥤ C) :=
  fun F => ∀ i j (f : i ⟶ j), W (F.map f)
abbrev Vertical (n : ℕ) := (allowed W n).FullSubcategory

def reindex {n m : ℕ} (u : Fin (n+1) ⥤ Fin (m+1)) : Strings W m ⥤ Strings W n where
  obj F := ⟨u ⋙ F.obj⟩
  map f := ⟨Functor.whiskerLeft u f.hom,fun i => f.property (u.obj i)⟩
  map_id _ := by apply WideSubcategory.hom_ext; rfl
  map_comp _ _ := by apply WideSubcategory.hom_ext; rfl
lemma reindex_id (n : ℕ) : reindex W (𝟭 (Fin (n+1)))=𝟭 _ := by
  refine CategoryTheory.Functor.ext (fun object => by cases object; rfl) ?_
  intro source target arrow
  erw [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl
lemma reindex_comp {n m k : ℕ} (u : Fin (n+1) ⥤ Fin (m+1)) (v : Fin (m+1) ⥤ Fin (k+1)) :
    reindex W (u⋙v)=reindex W v ⋙ reindex W u := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro source target arrow
  erw [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

def vreindex {n m : ℕ} (u : Fin (n+1) ⥤ Fin (m+1)) : Vertical W m ⥤ Vertical W n where
  obj F := ⟨u ⋙ F.obj,fun i j f => F.property (u.obj i) (u.obj j) (u.map f)⟩
  map f := ObjectProperty.homMk (Functor.whiskerLeft u f.hom)
  map_id _ := by apply ObjectProperty.hom_ext; rfl
  map_comp _ _ := by apply ObjectProperty.hom_ext; rfl
omit [W.IsMultiplicative] in
lemma vreindex_id (n : ℕ) : vreindex W (𝟭 (Fin (n+1)))=𝟭 _ := by
  refine CategoryTheory.Functor.ext (fun object => by cases object; rfl) ?_
  intro source target arrow
  erw [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl
omit [W.IsMultiplicative] in
lemma vreindex_comp {n m k : ℕ} (u : Fin (n+1) ⥤ Fin (m+1)) (v : Fin (m+1) ⥤ Fin (k+1)) :
    vreindex W (u⋙v)=vreindex W v ⋙ vreindex W u := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro source target arrow
  erw [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

def constant (n : ℕ) : C ⥤ Vertical W n where
  obj U := ⟨(Functor.const (Fin (n+1))).obj U,fun _ _ _ => W.id_mem U⟩
  map f := ObjectProperty.homMk ((Functor.const (Fin (n+1))).map f)
def evaluation (n : ℕ) : Vertical W n ⥤ C where
  obj F := F.obj.obj 0
  map f := f.hom.app 0
noncomputable def constantComparison (n : ℕ) : evaluation W n ⋙ constant W n ≅ 𝟭 _ :=
  NatIso.ofComponents (fun F => {
    hom := ObjectProperty.homMk {
      app i := F.obj.map (homOfLE (Fin.zero_le i))
      naturality i j f := by
        change 𝟙 _ ≫ F.obj.map _ = F.obj.map _ ≫ F.obj.map _
        rw [Category.id_comp,←F.obj.map_comp]
        congr 1 }
    inv := ObjectProperty.homMk {
      app i := by
        change F.obj.obj i ⟶ F.obj.obj 0
        exact inv (F.obj.map (homOfLE (Fin.zero_le i)))
      naturality i j f := by
        change F.obj.map f ≫ inv (F.obj.map _) = inv (F.obj.map _) ≫ 𝟙 _
        rw [Category.comp_id]
        apply (cancel_mono (F.obj.map (homOfLE (Fin.zero_le j)))).mp
        simp only [Category.assoc,IsIso.inv_hom_id,Category.comp_id]
        have he : F.obj.map (homOfLE (Fin.zero_le j)) =
            F.obj.map (homOfLE (Fin.zero_le i)) ≫ F.obj.map f := by
          rw [←F.obj.map_comp]; congr 1
        rw [he,←Category.assoc,IsIso.inv_hom_id,Category.id_comp] }
    hom_inv_id := by apply ObjectProperty.hom_ext; ext i; exact IsIso.hom_inv_id _
    inv_hom_id := by
      apply ObjectProperty.hom_ext
      ext i
      exact IsIso.inv_hom_id (F.obj.map (homOfLE (Fin.zero_le i))) })
    (by
      intro F G f
      apply ObjectProperty.hom_ext; ext i
      exact (f.hom.naturality _).symm)
noncomputable def equivalence (n : ℕ) : C ≌ Vertical W n where
  functor := constant W n
  inverse := evaluation W n
  unitIso := Iso.refl _
  counitIso := constantComparison W n
  functor_unitIso_comp U := by
    apply ObjectProperty.hom_ext; ext i
    change 𝟙 U ≫ 𝟙 U = 𝟙 U
    exact Category.id_comp _
noncomputable instance (n : ℕ) : (constant W n).IsEquivalence :=
  (equivalence W n).isEquivalence_functor

def horizontal : SimplicialObject Cat.{0,0} where
  obj p := Cat.of (Strings W p.unop.len)
  map f := (reindex W f.unop.toOrderHom.toFunctor).toCatHom
  map_id p := by apply Cat.ext; exact reindex_id W p.unop.len
  map_comp f g := by apply Cat.ext; exact reindex_comp W g.unop.toOrderHom.toFunctor f.unop.toOrderHom.toFunctor
def vertical : SimplicialObject Cat.{0,0} where
  obj p := Cat.of (Vertical W p.unop.len)
  map f := (vreindex W f.unop.toOrderHom.toFunctor).toCatHom
  map_id p := by apply Cat.ext; exact vreindex_id W p.unop.len
  map_comp f g := by apply Cat.ext; exact vreindex_comp W g.unop.toOrderHom.toFunctor f.unop.toOrderHom.toFunctor
def constantMap : (Functor.const SimplexCategoryᵒᵖ).obj (Cat.of C) ⟶ vertical W where
  app p := (constant W p.unop.len).toCatHom
  naturality _ _ f := by
    apply Cat.ext
    refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
    intro source target arrow
    erw [eqToHom_refl, Category.id_comp, Category.comp_id]
    exact (Category.id_comp _).symm

def transpose {p q : ℕ} (F : Fin (q+1) ⥤ Strings W p) : Fin (p+1) ⥤ Vertical W q where
  obj i := ⟨{
    obj j := (F.obj j).obj.obj i
    map f := (F.map f).hom.app i
    map_id j := by have h := F.map_id j; exact congrArg (fun x => x.hom.app i) h
    map_comp f g := by have h := F.map_comp f g; exact congrArg (fun x => x.hom.app i) h },
    fun j k f => (F.map f).property i⟩
  map f := ObjectProperty.homMk {
    app j := (F.obj j).obj.map f
    naturality j k g := ((F.map g).hom.naturality f).symm }
  map_id i := by apply ObjectProperty.hom_ext; ext j; exact (F.obj j).obj.map_id i
  map_comp f g := by apply ObjectProperty.hom_ext; ext j; exact (F.obj j).obj.map_comp f g

def untranspose {p q : ℕ} (F : Fin (p+1) ⥤ Vertical W q) : Fin (q+1) ⥤ Strings W p where
  obj i := ⟨{
    obj j := (F.obj j).obj.obj i
    map f := (F.map f).hom.app i
    map_id j := by have h := F.map_id j; exact congrArg (fun x => x.hom.app i) h
    map_comp f g := by have h := F.map_comp f g; exact congrArg (fun x => x.hom.app i) h }⟩
  map f := ⟨{
    app j := (F.obj j).obj.map f
    naturality j k g := ((F.map g).hom.naturality f).symm },
    fun i => (F.obj i).property _ _ f⟩
  map_id i := by apply WideSubcategory.hom_ext; ext j; exact (F.obj j).obj.map_id i
  map_comp f g := by apply WideSubcategory.hom_ext; ext j; exact (F.obj j).obj.map_comp f g
lemma untranspose_transpose {p q : ℕ} (F : Fin (q+1) ⥤ Strings W p) :
    untranspose W (transpose W F)=F := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro source target arrow
  erw [eqToHom_refl, Category.id_comp, Category.comp_id]
  apply WideSubcategory.hom_ext
  ext index
  rfl
lemma transpose_untranspose {p q : ℕ} (F : Fin (p+1) ⥤ Vertical W q) :
    transpose W (untranspose W F)=F := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro source target arrow
  erw [eqToHom_refl, Category.id_comp, Category.comp_id]
  apply ObjectProperty.hom_ext
  ext index
  rfl
noncomputable def diagonalIso : SimplicialDiagonal.nerveDiagonal.obj (horizontal W) ≅
    SimplicialDiagonal.nerveDiagonal.obj (vertical W) :=
  NatIso.ofComponents (fun p => Equiv.toIso {
    toFun := transpose W
    invFun := untranspose W
    left_inv := untranspose_transpose W
    right_inv := transpose_untranspose W }) (by
      intro p q f
      ext t
      refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
      intro source target arrow
      erw [eqToHom_refl, Category.id_comp, Category.comp_id]
      apply ObjectProperty.hom_ext
      ext index
      rfl)
noncomputable def constantDiagonalIso :
    SimplicialDiagonal.nerveDiagonal.obj ((Functor.const SimplexCategoryᵒᵖ).obj (Cat.of C)) ≅ nerve C :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)
noncomputable def homologyIso (n : ℕ) :
    (SimplicialDiagonal.nerveDiagonal.obj (horizontal W)).homology DiagonalResolution.Z n ≅
      (nerve C).homology DiagonalResolution.Z n := by
  haveI := SimplicialDiagonal.nerveDiagonal_isIso (constantMap W)
    (fun p => inferInstanceAs (constant W p.unop.len).IsEquivalence) n
  exact (SSet.homologyFunctor DiagonalResolution.Z n).mapIso (diagonalIso W) ≪≫
    (asIso (SSet.homologyMap (SimplicialDiagonal.nerveDiagonal.map (constantMap W))
      DiagonalResolution.Z n)).symm ≪≫
    (SSet.homologyFunctor DiagonalResolution.Z n).mapIso (constantDiagonalIso (C:=C))
end RestrictedNerve

end OAI
