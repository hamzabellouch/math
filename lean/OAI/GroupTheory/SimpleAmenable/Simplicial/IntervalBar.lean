import Mathlib

namespace OAI

section

section

open CategoryTheory MonoidalCategory
universe u v w
namespace IntervalBar
variable (C : Type u) [Groupoid.{v} C] [MonoidalCategory C]
variable (I : Type w) [Preorder I]

structure Diagram where
  obj : ∀ i j : I, i ≤ j → C
  unit : ∀ i, obj i i le_rfl ≅ 𝟙_ C
  cut : ∀ i j k (hij : i≤j) (hjk : j≤k), obj i j hij ⊗ obj j k hjk ≅ obj i k (hij.trans hjk)
  left_unit : ∀ i j (h : i≤j), (cut i i j le_rfl h).hom =
    (unit i).hom ▷ obj i j h ≫ (λ_ (obj i j h)).hom
  right_unit : ∀ i j (h : i≤j), (cut i j j h le_rfl).hom =
    obj i j h ◁ (unit j).hom ≫ (ρ_ (obj i j h)).hom
  associativity : ∀ i j k l (hij : i≤j) (hjk : j≤k) (hkl : k≤l),
    (cut i j k hij hjk).hom ▷ obj k l hkl ≫ (cut i k l (hij.trans hjk) hkl).hom =
    (α_ (obj i j hij) (obj j k hjk) (obj k l hkl)).hom ≫
      obj i j hij ◁ (cut j k l hjk hkl).hom ≫ (cut i j l hij (hjk.trans hkl)).hom

namespace Diagram
variable {C I}
structure Hom (D E : Diagram C I) where
  app : ∀ i j (h : i≤j), D.obj i j h ⟶ E.obj i j h
  unit : ∀i, app i i le_rfl ≫ (E.unit i).hom = (D.unit i).hom
  cut : ∀i j k (hij : i≤j) (hjk : j≤k),
    (app i j hij ⊗ₘ app j k hjk) ≫ (E.cut i j k hij hjk).hom =
      (D.cut i j k hij hjk).hom ≫ app i k (hij.trans hjk)

@[ext] lemma Hom.ext {D E : Diagram C I} {f g : Hom D E}
    (h : ∀i j hij,f.app i j hij=g.app i j hij) : f=g := by
  cases f; cases g
  simp_all only [mk.injEq]
  funext i j hij
  exact h i j hij

def Hom.id (D : Diagram C I) : Hom D D where
  app i j h := 𝟙 _
  unit i := by simp
  cut i j k hij hjk := by simp

def Hom.comp {D E F : Diagram C I} (f : Hom D E) (g : Hom E F) : Hom D F where
  app i j h := f.app i j h ≫ g.app i j h
  unit i := by rw [Category.assoc,g.unit,f.unit]
  cut i j k hij hjk := by
    rw [←tensorHom_comp_tensorHom,Category.assoc,g.cut,←Category.assoc,f.cut,Category.assoc]

noncomputable def Hom.inv {D E : Diagram C I} (f : Hom D E) : Hom E D where
  app i j h := CategoryTheory.inv (f.app i j h)
  unit i := by rw [←f.unit,←Category.assoc,IsIso.inv_hom_id,Category.id_comp]
  cut i j k hij hjk := by
    apply (cancel_epi (f.app i j hij ⊗ₘ f.app j k hjk)).mp
    simp only [←Category.assoc,tensorHom_comp_tensorHom,IsIso.hom_inv_id,id_tensorHom_id,
      Category.id_comp]
    rw [f.cut,Category.assoc,IsIso.hom_inv_id,Category.comp_id]

noncomputable instance : Groupoid (Diagram C I) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp f := by ext; simp [Hom.comp,Hom.id]
  comp_id f := by ext; simp [Hom.comp,Hom.id]
  assoc f g h := by ext; simp [Hom.comp,Category.assoc]
  inv := Hom.inv
  inv_comp f := by ext; simp [Hom.comp,Hom.inv,Hom.id]
  comp_inv f := by ext; simp [Hom.comp,Hom.inv,Hom.id]

@[simp] lemma id_app (D : Diagram C I) (i j : I) (h : i≤j) :
    (𝟙 D : D ⟶ D).app i j h=𝟙 _ := rfl
@[simp] lemma comp_app {D E F : Diagram C I} (f : D ⟶ E) (g : E ⟶ F)
    (i j : I) (h : i≤j) : (f≫g).app i j h=f.app i j h≫g.app i j h := rfl

variable {J : Type w} [Preorder J]
def reindexObj (f : I →o J) (D : Diagram C J) : Diagram C I where
  obj i j h := D.obj (f i) (f j) (f.monotone h)
  unit i := D.unit (f i)
  cut i j k hij hjk := D.cut (f i) (f j) (f k) (f.monotone hij) (f.monotone hjk)
  left_unit i j h := D.left_unit (f i) (f j) (f.monotone h)
  right_unit i j h := D.right_unit (f i) (f j) (f.monotone h)
  associativity i j k l hij hjk hkl :=
    D.associativity (f i) (f j) (f k) (f l) (f.monotone hij) (f.monotone hjk) (f.monotone hkl)

noncomputable def reindex (f : I →o J) : Diagram C J ⥤ Diagram C I where
  obj := reindexObj f
  map g := {
    app i j h := g.app (f i) (f j) (f.monotone h)
    unit i := g.unit (f i)
    cut i j k hij hjk := g.cut (f i) (f j) (f k) (f.monotone hij) (f.monotone hjk) }

@[simp] lemma reindex_id : reindex (C:=C) (OrderHom.id : I →o I)=𝟭 _ := by
  apply CategoryTheory.Functor.ext
  case h_obj => intro D; cases D; rfl
  case h_map => intro D E f; change _ = (𝟙 _ ≫ f ≫ 𝟙 _); simp only [Category.id_comp,Category.comp_id]; rfl

variable {K : Type w} [Preorder K]
@[simp] lemma reindex_comp (f : I →o J) (g : J →o K) :
    reindex (C:=C) (g.comp f)=reindex g ⋙ reindex f := by
  apply CategoryTheory.Functor.ext
  case h_obj => intro D; rfl
  case h_map => intro D E h; change _ = (𝟙 _ ≫ (reindex g ⋙ reindex f).map h ≫ 𝟙 _); simp only [Category.id_comp,Category.comp_id]; rfl

noncomputable def eval (n : ℕ) : Diagram C (Fin (n+1)) ⥤ (Fin n → C) where
  obj D i := D.obj i.castSucc i.succ (Fin.castSucc_le_succ i)
  map f i := f.app i.castSucc i.succ (Fin.castSucc_le_succ i)

lemma hom_ext_elementary {n : ℕ} {D E : Diagram C (Fin (n+1))} (f g : D ⟶ E)
    (h : ∀ i : Fin n, f.app i.castSucc i.succ (Fin.castSucc_le_succ i) =
      g.app i.castSucc i.succ (Fin.castSucc_le_succ i)) : f=g := by
  have diag (i : Fin (n+1)) : f.app i i le_rfl=g.app i i le_rfl := by
    apply (cancel_mono (E.unit i).hom).mp
    rw [f.unit,g.unit]
  apply Hom.ext
  suffices ∀ j : Fin (n+1), ∀ i (hij : i≤j), f.app i j hij=g.app i j hij by
    intro i j hij; exact this j i hij
  apply Fin.induction
  · intro i hi
    have : i=0 := Fin.eq_of_val_eq (by simpa using hi)
    subst i
    exact diag 0
  · intro j ih i hij
    by_cases he : i=j.succ
    · subst i; exact diag j.succ
    · have hi : i≤j.castSucc := by
        simp only [Fin.le_def,Fin.ext_iff,Fin.val_succ,Fin.val_castSucc] at *
        omega
      apply (cancel_epi (D.cut i j.castSucc j.succ hi (Fin.castSucc_le_succ j)).hom).mp
      rw [←f.cut,←g.cut,ih i hi,h j]

noncomputable instance (n : ℕ) : (eval (C:=C) n).Faithful where
  map_injective {_ _} f g h := hom_ext_elementary f g (fun i => congrFun h i)

open scoped Simplicial
noncomputable def simplicial : SimplicialObject Cat.{v,max u v} where
  obj n := Cat.of (Diagram C (Fin (n.unop.len+1)))
  map f := (reindex f.unop.toOrderHom).toCatHom
  map_id n := by
    apply Cat.ext
    exact reindex_id
  map_comp f g := by
    apply Cat.ext
    exact reindex_comp g.unop.toOrderHom f.unop.toOrderHom

end Diagram
end IntervalBar

end

end

end OAI
