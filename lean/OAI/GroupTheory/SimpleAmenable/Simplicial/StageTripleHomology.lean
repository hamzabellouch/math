import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.DiagonalComparison
import OAI.GroupTheory.SimpleAmenable.Configurations.StageIteratedMaps2
import OAI.GroupTheory.SimpleAmenable.Homology.PowerEquivalence

namespace OAI

section

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory
namespace ColimitTransfer

universe u v
variable {J : Type} {A : Type u} [Category.{0} J] [Category.{v} A]
noncomputable def transportDiagram (F : J ⥤ A) (X : J → A) (e : ∀j,X j≅F.obj j) : J ⥤ A where
  obj := X
  map {i j} f := (e i).hom ≫ F.map f ≫ (e j).inv
  map_id i := by simp
  map_comp f g := by simp [Category.assoc]
noncomputable def transportIso (F : J ⥤ A) (X : J → A) (e : ∀j,X j≅F.obj j) :
    transportDiagram F X e ≅ F := NatIso.ofComponents e (by intro i j f; simp [transportDiagram])
noncomputable def transportCocone {F : J ⥤ A} (s : Cocone F) (X : J → A)
    (e : ∀j,X j≅F.obj j) (Y : A) (d : Y≅s.pt) : Cocone (transportDiagram F X e) where
  pt := Y
  ι := { app j := (e j).hom ≫ s.ι.app j ≫ d.inv
         naturality i j f := by simp [transportDiagram,Category.assoc] }
noncomputable def transportIsColimit {F : J ⥤ A} (s : Cocone F) (X : J → A)
    (e : ∀j,X j≅F.obj j) (Y : A) (d : Y≅s.pt) (hs : IsColimit s) :
    IsColimit (transportCocone s X e Y d) := by
  let pointIso : (transportCocone s X e Y d).pt ≅ s.pt := d
  refine ofIsos (transportCocone s X e Y d) s (transportIso F X e).hom pointIso.hom ?_ hs
  intro j
  change ((e j).hom ≫ s.ι.app j ≫ d.inv) ≫ d.hom =
    (e j).hom ≫ s.ι.app j
  simp [Category.assoc]
end ColimitTransfer
namespace IntervalBar.Diagram
variable {C D : Type} [Groupoid.{0} C] [Groupoid.{0} D]
  [MonoidalCategory C] [MonoidalCategory D] [SymmetricCategory C] [SymmetricCategory D]
noncomputable instance map₂Monoidal (F : C ⥤ D) [F.Braided] (m n : ℕ) :
    (map (I:=Fin (m+1)) (map (I:=Fin (n+1)) F)).Monoidal := by
  letI : (map (I:=Fin (n+1)) F).Braided := mapBraided F
  exact mapMonoidal _
end IntervalBar.Diagram
namespace SimpleAmenable.PolygonObject.LabelledStage.Stage
open StageProductColimit IntervalBar IntervalBar.Diagram ColimitTransfer

variable {a n : ℕ} (l m p q : ℕ)
noncomputable abbrev tripleDegree (C : Type) [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C] :=
  Diagram (Diagram (Diagram C (Fin (p+1))) (Fin (m+1))) (Fin (l+1))
noncomputable def tripleEvalIso (C : Type) [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C] :
    (H q).obj (Cat.of (tripleDegree l m p C)) ≅ (H q).obj (Cat.of (Fin l × (Fin m × Fin p) → C)) :=
  NerveHomotopy.homologyIso (eval₃ l m p).asEquivalence (ModuleCat.of ℤ ℤ) q
noncomputable def tripleHomologyStage : Stage a n ⥤ ModuleCat ℤ :=
  transportDiagram (productStage (a:=a) (n:=n) (Fin l × (Fin m × Fin p)) ⋙ H q)
    (fun S => (H q).obj (Cat.of (tripleDegree l m p S.Obj)))
    (fun S => tripleEvalIso l m p q S.Obj)
noncomputable def tripleHomologyCocone : Cocone (tripleHomologyStage (a:=a) (n:=n) l m p q) :=
  transportCocone ((H q).mapCocone (productCocone (a:=a) (n:=n) (Fin l × (Fin m × Fin p))))
    (fun S => (H q).obj (Cat.of (tripleDegree l m p S.Obj)))
    (fun S => tripleEvalIso l m p q S.Obj)
    ((H q).obj (Cat.of (tripleDegree l m p (Labelled a n))))
    (tripleEvalIso l m p q (Labelled a n))

noncomputable def tripleHomologyIsColimit :
    IsColimit (tripleHomologyCocone (a:=a) (n:=n) l m p q) :=
  transportIsColimit _ _ _ _ _ (productHomologyIsColimit _ q)
variable {C D : Type} [Groupoid.{0} C] [Groupoid.{0} D]
    [MonoidalCategory C] [MonoidalCategory D] [SymmetricCategory C] [SymmetricCategory D]
lemma tripleEvalIso_hom (C : Type) [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C] :
    (tripleEvalIso l m p q C).hom = (H q).map (eval₃ (C:=C) l m p).toCatHom := rfl
lemma tripleEval_naturality (F : C ⥤ D) [F.Braided] :
    (H q).map (Diagram.map (I:=Fin (l+1)) (Diagram.map (I:=Fin (m+1))
      (Diagram.map (I:=Fin (p+1)) F))).toCatHom ≫ (tripleEvalIso l m p q D).hom =
      (tripleEvalIso l m p q C).hom ≫ (H q).map (powerMap (Fin l × (Fin m × Fin p)) F).toCatHom := by
  rw [tripleEvalIso_hom,tripleEvalIso_hom]
  rw [←Functor.map_comp,←Functor.map_comp]
  apply congrArg (H q).map
  apply Cat.ext
  exact eval₃_natural F l m p

lemma tripleHomologyStage_map {S T : Stage a n} (h:S⟶T) :
    (tripleHomologyStage l m p q).map h =
      (H q).map (Diagram.map (I:=Fin (l+1)) (Diagram.map (I:=Fin (m+1))
        (Diagram.map (I:=Fin (p+1)) (inclusion (leOfHom h))))).toCatHom := by
  change (tripleEvalIso l m p q S.Obj).hom ≫
    (H q).map (powerMap (Fin l × (Fin m × Fin p)) (inclusion (leOfHom h))).toCatHom ≫
    (tripleEvalIso l m p q T.Obj).inv = _
  rw [←Category.assoc]
  exact (Iso.comp_inv_eq _).mpr (tripleEval_naturality l m p q (inclusion (leOfHom h))).symm
lemma tripleHomologyCocone_ι (S : Stage a n) :
    (tripleHomologyCocone l m p q).ι.app S =
      (H q).map (Diagram.map (I:=Fin (l+1)) (Diagram.map (I:=Fin (m+1))
        (Diagram.map (I:=Fin (p+1)) S.forget))).toCatHom := by
  change (tripleEvalIso l m p q S.Obj).hom ≫
    (H q).map (powerMap (Fin l × (Fin m × Fin p)) S.forget).toCatHom ≫
    (tripleEvalIso l m p q (Labelled a n)).inv = _
  rw [←Category.assoc]
  exact (Iso.comp_inv_eq _).mpr (tripleEval_naturality l m p q S.forget).symm
end SimpleAmenable.PolygonObject.LabelledStage.Stage

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory
namespace IntervalBar.Diagram

variable {C D : Type} [Groupoid.{0} C] [Groupoid.{0} D]
  [MonoidalCategory C] [MonoidalCategory D] [SymmetricCategory C] [SymmetricCategory D]
@[simp] lemma map₂_η_app (F : C ⥤ D) [F.Braided] (m p:ℕ)
    (i j:Fin (m+1)) (hij:i≤j) (v w:Fin (p+1)) (hvw:v≤w) :
    ((Functor.OplaxMonoidal.η (map (I:=Fin (m+1)) (map (I:=Fin (p+1)) F))).app i j hij).app v w hvw =
      Functor.OplaxMonoidal.η F := by
  exact (congrArg (fun f => f.app v w hvw) (map_η_app (map (I:=Fin (p+1)) F) i j hij)).trans
    (map_η_app F v w hvw)
@[simp] lemma map₂_μ_app (F : C ⥤ D) [F.Braided] (m p:ℕ)
    (A B : Diagram (Diagram C (Fin (p+1))) (Fin (m+1)))
    (i j:Fin (m+1)) (hij:i≤j) (v w:Fin (p+1)) (hvw:v≤w) :
    ((Functor.LaxMonoidal.μ (map (I:=Fin (m+1)) (map (I:=Fin (p+1)) F)) A B).app i j hij).app v w hvw =
      Functor.LaxMonoidal.μ F ((A.obj i j hij).obj v w hvw) ((B.obj i j hij).obj v w hvw) := rfl
end IntervalBar.Diagram
namespace SimpleAmenable.PolygonObject.LabelledStage.Stage
open IntervalBar IntervalBar.Diagram

variable {a n : ℕ} (l m p : ℕ)
lemma map₃_inclusion_comp_obj {S T U : Stage a n} (h:S≤T) (k:T≤U)
    (A : tripleDegree l m p S.Obj) :
    mapObj (Diagram.map (I:=Fin (m+1)) (Diagram.map (I:=Fin (p+1)) (inclusion (h.trans k)))) A =
      mapObj (Diagram.map (Diagram.map (inclusion k))) (mapObj (Diagram.map (Diagram.map (inclusion h))) A) := by
  have he (X : Diagram (Diagram S.Obj (Fin (p+1))) (Fin (m+1))) :
      mapObj (Diagram.map (inclusion (h.trans k))) X=
        mapObj (Diagram.map (inclusion k)) (mapObj (Diagram.map (inclusion h)) X) :=
    map₂_inclusion_comp_obj h k X
  have he₁ (X : Diagram S.Obj (Fin (p+1))) : mapObj (inclusion (h.trans k)) X=
      mapObj (inclusion k) (mapObj (inclusion h) X) :=
    congrArg (fun F=>F.obj X) (map_inclusion_comp h k)
  refine ext_heq ?_ ?_ ?_
  · funext i j hij; exact he _
  · apply hfunext; intro i
    apply iso_hext (he _) rfl
    apply hom_hext (he _) rfl
    intro j z hjz
    apply hom_hext (he₁ _) rfl
    intro v w hvw
    apply heq_of_eq
    change (inclusion (h.trans k)).map (((A.unit i).hom.app j z hjz).app v w hvw) ≫
      ((Functor.OplaxMonoidal.η (Diagram.map (I:=Fin (m+1))
        (Diagram.map (I:=Fin (p+1)) (inclusion (h.trans k))))).app j z hjz).app v w hvw =
      (inclusion k).map ((inclusion h).map (((A.unit i).hom.app j z hjz).app v w hvw) ≫
        ((Functor.OplaxMonoidal.η (Diagram.map (I:=Fin (m+1))
          (Diagram.map (I:=Fin (p+1)) (inclusion h)))).app j z hjz).app v w hvw) ≫
      ((Functor.OplaxMonoidal.η (Diagram.map (I:=Fin (m+1))
        (Diagram.map (I:=Fin (p+1)) (inclusion k)))).app j z hjz).app v w hvw
    simp only [map₂_η_app,inclusion_η]
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
    simp only [mapObj,Functor.mapIso_hom,Iso.trans_hom,Functor.Monoidal.μIso_hom,
      map₂_μ_app,comp_app,map_map_app,inclusion_μ,Functor.map_comp]
    rfl
lemma map₃_inclusion_comp {S T U : Stage a n} (h:S≤T) (k:T≤U) :
    Diagram.map (I:=Fin (l+1)) (Diagram.map (I:=Fin (m+1)) (Diagram.map (I:=Fin (p+1)) (inclusion (h.trans k)))) =
      Diagram.map (Diagram.map (Diagram.map (inclusion h))) ⋙ Diagram.map (Diagram.map (Diagram.map (inclusion k))) := by
  refine CategoryTheory.Functor.hext (map₃_inclusion_comp_obj l m p h k) ?_
  intro A B f
  apply hom_hext (map₃_inclusion_comp_obj l m p h k A) (map₃_inclusion_comp_obj l m p h k B)
  intro i j hij
  apply hom_hext (map₂_inclusion_comp_obj h k _) (map₂_inclusion_comp_obj h k _)
  intro v w hvw
  apply hom_hext
    (congrArg (fun F => F.obj ((A.obj i j hij).obj v w hvw)) (map_inclusion_comp h k))
    (congrArg (fun F => F.obj ((B.obj i j hij).obj v w hvw)) (map_inclusion_comp h k))
  intro x y hxy
  rfl
lemma map₃_inclusion_forget_obj {S T : Stage a n} (h:S≤T)
    (A : tripleDegree l m p S.Obj) :
    mapObj (Diagram.map (Diagram.map T.forget))
      (mapObj (Diagram.map (I:=Fin (m+1)) (Diagram.map (I:=Fin (p+1)) (inclusion h))) A) =
      mapObj (Diagram.map (Diagram.map S.forget)) A := by
  have he (X : Diagram (Diagram S.Obj (Fin (p+1))) (Fin (m+1))) :
      mapObj (Diagram.map T.forget) (mapObj (Diagram.map (inclusion h)) X)=
        mapObj (Diagram.map S.forget) X := map₂_inclusion_forget_obj h X
  have he₁ (X : Diagram S.Obj (Fin (p+1))) : mapObj T.forget (mapObj (inclusion h) X)=
      mapObj S.forget X := congrArg (fun F=>F.obj X) (map_inclusion_forget h)
  refine ext_heq ?_ ?_ ?_
  · funext i j hij; exact he _
  · apply hfunext; intro i
    apply iso_hext (he _) rfl
    apply hom_hext (he _) rfl
    intro j z hjz
    apply hom_hext (he₁ _) rfl
    intro v w hvw
    apply heq_of_eq
    change T.forget.map ((inclusion h).map (((A.unit i).hom.app j z hjz).app v w hvw) ≫
      ((Functor.OplaxMonoidal.η (Diagram.map (I:=Fin (m+1))
        (Diagram.map (I:=Fin (p+1)) (inclusion h)))).app j z hjz).app v w hvw) ≫
      ((Functor.OplaxMonoidal.η (Diagram.map (I:=Fin (m+1))
        (Diagram.map (I:=Fin (p+1)) T.forget))).app j z hjz).app v w hvw =
      S.forget.map (((A.unit i).hom.app j z hjz).app v w hvw) ≫
      ((Functor.OplaxMonoidal.η (Diagram.map (I:=Fin (m+1))
        (Diagram.map (I:=Fin (p+1)) S.forget))).app j z hjz).app v w hvw
    simp only [map₂_η_app,inclusion_η,forget_η]
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
    simp only [mapObj,Functor.mapIso_hom,Iso.trans_hom,Functor.Monoidal.μIso_hom,
      map₂_μ_app,comp_app,map_map_app,forget_μ,Functor.map_comp]
    rfl
lemma map₃_inclusion_forget {S T : Stage a n} (h:S≤T) :
    Diagram.map (I:=Fin (l+1)) (Diagram.map (I:=Fin (m+1)) (Diagram.map (I:=Fin (p+1)) (inclusion h))) ⋙
      Diagram.map (Diagram.map (Diagram.map T.forget)) = Diagram.map (Diagram.map (Diagram.map S.forget)) := by
  refine CategoryTheory.Functor.hext (map₃_inclusion_forget_obj l m p h) ?_
  intro A B f
  apply hom_hext (map₃_inclusion_forget_obj l m p h A) (map₃_inclusion_forget_obj l m p h B)
  intro i j hij
  apply hom_hext (map₂_inclusion_forget_obj h _) (map₂_inclusion_forget_obj h _)
  intro v w hvw
  apply hom_hext
    (congrArg (fun F => F.obj ((A.obj i j hij).obj v w hvw)) (map_inclusion_forget h))
    (congrArg (fun F => F.obj ((B.obj i j hij).obj v w hvw)) (map_inclusion_forget h))
  intro x y hxy
  rfl
lemma map₃_inclusion_id_obj (S : Stage a n) (A : tripleDegree l m p S.Obj) :
    mapObj (Diagram.map (I:=Fin (m+1)) (Diagram.map (I:=Fin (p+1)) (inclusion (le_refl S)))) A=A := by
  have he (X : Diagram (Diagram S.Obj (Fin (p+1))) (Fin (m+1))) :
      mapObj (Diagram.map (inclusion (le_refl S))) X=X :=
    congrArg (fun F=>F.obj X) (map₂_inclusion_id S)
  have he₁ (X : Diagram S.Obj (Fin (p+1))) : mapObj (inclusion (le_refl S)) X=X :=
    congrArg (fun F=>F.obj X) (map_inclusion_id S)
  refine ext_heq ?_ ?_ ?_
  · funext i j hij; exact he _
  · apply hfunext; intro i
    apply iso_hext (he _) rfl
    apply hom_hext (he _) rfl
    intro j z hjz
    apply hom_hext (he₁ _) rfl
    intro v w hvw
    apply heq_of_eq
    change (inclusion (le_refl S)).map (((A.unit i).hom.app j z hjz).app v w hvw) ≫
      ((Functor.OplaxMonoidal.η (Diagram.map (I:=Fin (m+1))
        (Diagram.map (I:=Fin (p+1)) (inclusion (le_refl S))))).app j z hjz).app v w hvw =
      ((A.unit i).hom.app j z hjz).app v w hvw
    rw [map₂_η_app,inclusion_η]
    apply UniformObject.Hom.ext
    exact Category.comp_id _
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
    simp only [mapObj,Functor.mapIso_hom,Iso.trans_hom,Functor.Monoidal.μIso_hom,
      comp_app,map_map_app]
    rfl
lemma map₃_inclusion_id (S : Stage a n) :
    Diagram.map (I:=Fin (l+1)) (Diagram.map (I:=Fin (m+1)) (Diagram.map (I:=Fin (p+1)) (inclusion (le_refl S))))=𝟭 _ := by
  refine CategoryTheory.Functor.hext (map₃_inclusion_id_obj l m p S) ?_
  intro A B f
  apply hom_hext (map₃_inclusion_id_obj l m p S A) (map₃_inclusion_id_obj l m p S B)
  intro i j hij
  apply hom_hext
    (congrArg (fun F => F.obj (A.obj i j hij)) (map₂_inclusion_id S))
    (congrArg (fun F => F.obj (B.obj i j hij)) (map₂_inclusion_id S))
  intro v w hvw
  apply hom_hext
    (congrArg (fun F => F.obj ((A.obj i j hij).obj v w hvw)) (map_inclusion_id S))
    (congrArg (fun F => F.obj ((B.obj i j hij).obj v w hvw)) (map_inclusion_id S))
  intro x y hxy
  rfl
end SimpleAmenable.PolygonObject.LabelledStage.Stage

end

end

end OAI
