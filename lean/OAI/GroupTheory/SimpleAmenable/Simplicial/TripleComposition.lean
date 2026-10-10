import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.TripleBarMaps
import OAI.GroupTheory.SimpleAmenable.Simplicial.StageTripleHomology

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory
namespace IntervalBar.Diagram

variable {C D E : Type} [Groupoid.{0} C] [Groupoid.{0} D] [Groupoid.{0} E]
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
  [SymmetricCategory C] [SymmetricCategory D] [SymmetricCategory E]
variable {I J K : Type} [Preorder I] [Preorder J] [Preorder K]
  (F:C ⥤ D) (G:D ⥤ E) [F.Braided] [G.Braided]
private lemma map_unit_component (A : Diagram (Diagram C I) J) (i : J)
    (j k : I) (h : j ≤ k) :
    ((mapObj (map F) A).unit i).hom.app j k h =
      F.map ((A.unit i).hom.app j k h) ≫ Functor.OplaxMonoidal.η F := by
  change ((map F).map (A.unit i).hom ≫ Functor.OplaxMonoidal.η (map F)).app j k h = _
  erw [comp_app, map_η_app (I:=I) F]
  rfl

private lemma map_cut_component (A : Diagram (Diagram C I) J) (i j k : J)
    (hij : i ≤ j) (hjk : j ≤ k) (l m : I) (h : l ≤ m) :
    ((mapObj (map F) A).cut i j k hij hjk).hom.app l m h =
      Functor.LaxMonoidal.μ F ((A.obj i j hij).obj l m h) ((A.obj j k hjk).obj l m h) ≫
        F.map ((A.cut i j k hij hjk).hom.app l m h) := rfl

lemma map₂_comp_obj (A : Diagram (Diagram C I) J) :
    mapObj (map (I:=I) (F⋙G)) A=mapObj (map G) (mapObj (map F) A) := by
  have he (X : Diagram C I) := mapObj_comp F G X
  refine ext_heq ?_ ?_ ?_
  · funext i j h; exact he _
  · apply hfunext; intro i
    apply iso_hext (he _) rfl
    apply hom_hext (he _) rfl
    intro j k h
    apply heq_of_eq
    erw [map_unit_component, map_unit_component, map_unit_component]
    simp only [Functor.comp_map, Functor.OplaxMonoidal.comp_η]
    erw [Functor.map_comp, Category.assoc]
    rfl
  · apply hfunext; intro i
    apply hfunext; intro j
    apply hfunext; intro k
    apply hfunext; intro hij
    apply hfunext; intro hjk
    apply iso_hext (congrArg₂ (fun X Y=>X⊗Y) (he _) (he _)) (he _)
    apply hom_hext (congrArg₂ (fun X Y=>X⊗Y) (he _) (he _)) (he _)
    intro l m h
    apply heq_of_eq
    erw [map_cut_component, map_cut_component, map_cut_component]
    simp only [Functor.LaxMonoidal.comp_μ]
    erw [Functor.map_comp, Category.assoc]
    rfl
lemma map₂_comp : map (I:=J) (map (I:=I) (F⋙G))=map (map F) ⋙ map (map G) := by
  refine CategoryTheory.Functor.hext (map₂_comp_obj F G) ?_
  intro A B f
  apply hom_hext (map₂_comp_obj F G A) (map₂_comp_obj F G B)
  intro i j hij
  apply hom_hext (mapObj_comp F G _) (mapObj_comp F G _)
  intro l m hlm
  rfl
lemma map₃_comp_obj (l m p : ℕ)
    (A : Diagram (Diagram (Diagram C (Fin (p+1))) (Fin (m+1))) (Fin (l+1))) :
    mapObj (map (I:=Fin (m+1)) (map (I:=Fin (p+1)) (F⋙G))) A =
      mapObj (map (map G)) (mapObj (map (map F)) A) := by
  have he (X : Diagram (Diagram C (Fin (p+1))) (Fin (m+1))) :
      mapObj (map (F⋙G)) X=
        mapObj (map G) (mapObj (map F) X) :=
    map₂_comp_obj F G X
  have he₁ (X : Diagram C (Fin (p+1))) : mapObj (F⋙G) X=
      mapObj G (mapObj F X) :=
    mapObj_comp F G X
  refine ext_heq ?_ ?_ ?_
  · funext i j hij; exact he _
  · apply hfunext; intro i
    apply iso_hext (he _) rfl
    apply hom_hext (he _) rfl
    intro j z hjz
    apply hom_hext (he₁ _) rfl
    intro v w hvw
    apply heq_of_eq
    erw [map_unit_component, map_unit_component, map_unit_component]
    erw [comp_app, comp_app, map_η_app, map_η_app]
    erw [map_map_app (I:=Fin (p+1)) G, comp_app,
      map_η_app (I:=Fin (p+1)) F]
    change G.map (F.map (((A.unit i).hom.app j z hjz).app v w hvw)) ≫
        Functor.OplaxMonoidal.η (F ⋙ G) =
      G.map (F.map (((A.unit i).hom.app j z hjz).app v w hvw) ≫
        Functor.OplaxMonoidal.η F) ≫ Functor.OplaxMonoidal.η G
    erw [Functor.OplaxMonoidal.comp_η, Functor.map_comp, Category.assoc]
    rfl
  · apply hfunext; intro i
    apply hfunext; intro j
    apply hfunext; intro z
    apply hfunext; intro hij
    apply hfunext; intro hjz
    apply iso_hext (congrArg₂ (fun X Y=>X⊗Y) (he _) (he _)) (he _)
    apply hom_hext (congrArg₂ (fun X Y=>X⊗Y) (he _) (he _)) (he _)
    intro v w hvw
    apply hom_hext (congrArg₂ (fun X Y=>X⊗Y) (he₁ _) (he₁ _)) (he₁ _)
    intro x y hxy
    apply heq_of_eq
    erw [map_cut_component, map_cut_component, map_cut_component]
    change Functor.LaxMonoidal.μ (F ⋙ G)
        (((A.obj i j hij).obj v w hvw).obj x y hxy)
        (((A.obj j z hjz).obj v w hvw).obj x y hxy) ≫
        G.map (F.map (((A.cut i j z hij hjz).hom.app v w hvw).app x y hxy)) =
      Functor.LaxMonoidal.μ G
        (F.obj (((A.obj i j hij).obj v w hvw).obj x y hxy))
        (F.obj (((A.obj j z hjz).obj v w hvw).obj x y hxy)) ≫
        G.map (Functor.LaxMonoidal.μ F
          (((A.obj i j hij).obj v w hvw).obj x y hxy)
          (((A.obj j z hjz).obj v w hvw).obj x y hxy) ≫
            F.map (((A.cut i j z hij hjz).hom.app v w hvw).app x y hxy))
    rw [Functor.LaxMonoidal.comp_μ, Functor.map_comp, Category.assoc]
lemma map₃_comp (l m p : ℕ) :
    map (I:=Fin (l+1)) (map (I:=Fin (m+1)) (map (I:=Fin (p+1)) (F⋙G))) =
      map (map (map F)) ⋙ map (map (map G)) := by
  refine CategoryTheory.Functor.hext (map₃_comp_obj F G l m p) ?_
  intro A B f
  apply hom_hext (map₃_comp_obj F G l m p A) (map₃_comp_obj F G l m p B)
  intro i j hij
  apply hom_hext (map₂_comp_obj F G _) (map₂_comp_obj F G _)
  intro v w hvw
  apply hom_hext
    (congrArg (fun F => F.obj ((A.obj i j hij).obj v w hvw)) (map_comp F G))
    (congrArg (fun F => F.obj ((B.obj i j hij).obj v w hvw)) (map_comp F G))
  intro x y hxy
  rfl
lemma bar₃Map_comp : bar₃Map (F⋙G)=bar₃Map F ≫ bar₃Map G := by
  ext n x
  exact congrArg (fun T => x ⋙ T) (map₃_comp F G n.unop.len n.unop.len n.unop.len)

end IntervalBar.Diagram

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory Simplicial Opposite
namespace BarFinitePower

section Swap
variable {C : Type} [Category.{0} C] (κ ι : Type)
def swap : (κ → ι → C) ⥤ (ι → κ → C) where
  obj X i k := X k i
  map f i k := f k i
noncomputable def swapEquiv : (κ → ι → C) ≌ (ι → κ → C) where
  functor := swap κ ι
  inverse := swap ι κ
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by intros; simp only [Iso.refl_hom]; erw [Category.comp_id, Category.id_comp]; rfl)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by intros; simp only [Iso.refl_hom]; erw [Category.comp_id, Category.id_comp]; rfl)
  functor_unitIso_comp := by
    intro X
    funext i k
    exact Category.id_comp (𝟙 (X k i))
instance : (swap (C:=C) κ ι).IsEquivalence := (swapEquiv κ ι).isEquivalence_functor
end Swap
variable {C : Type} (κ : Type) [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
open IntervalBar IntervalBar.Diagram StageProductColimit
noncomputable def project (k:κ) : (κ → C) ⥤ C := Pi.eval (fun _ : κ => C) k
noncomputable instance (k:κ) : (project (C:=C) κ k).Braided := inferInstanceAs ((Pi.eval (fun _ : κ => C) k).Braided)
noncomputable def tripleProject (l m n:ℕ) :
    Diagram (Diagram (Diagram (κ → C) (Fin (n+1))) (Fin (m+1))) (Fin (l+1)) ⥤
      (κ → Diagram (Diagram (Diagram C (Fin (n+1))) (Fin (m+1))) (Fin (l+1))) :=
  Functor.pi' (fun k => map (I:=Fin (l+1)) (map (I:=Fin (m+1)) (map (I:=Fin (n+1)) (project κ k))))
lemma tripleProject_eval (l m n:ℕ) :
    tripleProject (C:=C) κ l m n ⋙ powerMap κ (eval₃ l m n) =
      eval₃ l m n ⋙ swap (Fin l × (Fin m × Fin n)) κ := rfl
noncomputable instance (l m n:ℕ) : (tripleProject (C:=C) κ l m n).IsEquivalence := by
  have : (tripleProject (C:=C) κ l m n ⋙ powerMap κ (eval₃ l m n)).IsEquivalence := by
    rw [tripleProject_eval]
    infer_instance
  exact Functor.isEquivalence_of_comp_right _ (powerMap κ (eval₃ l m n))
end BarFinitePower

end

open _root_.CategoryTheory _root_.OAI.CategoryTheory Simplicial Opposite
namespace BarFinitePower

variable (κ : Type)
def power : SSet ⥤ SSet where
  obj X := {
    obj p := κ → X.obj p
    map f := ↾fun x k => X.map f (x k)
    map_id p := by ext x k; exact congrArg (fun f => f (x k)) (X.map_id p)
    map_comp f g := by ext x k; exact congrArg (fun f => f (x k)) (X.map_comp f g) }
  map f := {
    app p := ↾fun x k => f.app p (x k)
    naturality _ _ g := by ext x k; exact congrArg (fun f => f (x k)) (f.naturality g) }
  map_id _ := rfl
  map_comp _ _ := rfl
noncomputable def lift {X Y : SSet} (f : κ → (X ⟶ Y)) : X ⟶ (power κ).obj Y where
  app p := ↾fun x k => (f k).app p x
  naturality _ _ g := by
    apply ConcreteCategory.hom_ext; intro x; funext k
    exact congrArg (fun f => f x) ((f k).naturality g)
variable {C : Type} [Category.{0} C]
noncomputable def nervePiIso : nerve (κ → C) ≅ (power κ).obj (nerve C) where
  hom := lift κ (fun k => nerveMap (Pi.eval (fun _ : κ => C) k))
  inv := {
    app _ := ↾fun X => Functor.pi' X
    naturality _ _ _ := by ext X; rfl }
  hom_inv_id := by ext p X; rfl
  inv_hom_id := by ext p X; rfl
lemma lift_nerve {D : Type} [Category.{0} D] (F : κ → (D ⥤ C)) :
    lift κ (fun k => nerveMap (F k)) = nerveMap (Functor.pi' F) ≫ (nervePiIso κ).hom := rfl
lemma lift_nerve_homology_isIso {D : Type} [Category.{0} D] (F : κ → (D ⥤ C))
    [(Functor.pi' F).IsEquivalence] (n:ℕ) :
    IsIso (SSet.homologyMap (lift κ (fun k => nerveMap (F k))) DiagonalResolution.Z n) := by
  rw [lift_nerve,SSet.homologyMap_comp]
  infer_instance
end BarFinitePower

end OAI
