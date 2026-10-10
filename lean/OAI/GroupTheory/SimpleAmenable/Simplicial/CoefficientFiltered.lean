import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.CoefficientContraction
import OAI.GroupTheory.SimpleAmenable.Homology.ExactShapeHomology

namespace OAI

namespace CoefficientNerve

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits Simplicial SimplicialObject Opposite AlgebraicTopology

variable {R:Type} [CommRing R] {C:Type} [Category.{0} C]
variable (F:C ⥤ ModuleCat.{0} R)
lemma single_eq {n:ℕ} {s t:Simplex C n} (h:s=t)
    (e:Coeff F n s=Coeff F n t) : single F s=eqToHom e ≫ single F t := by
  subst t
  simp
def overLift {n:ℕ} (s:Simplex C n) : Simplex (Over s.left.unop) n where
  obj i := op (Over.mk ((s.map (homOfLE (Fin.zero_le i))).unop))
  map {i j} f := (Over.homMk (s.map f).unop (by
    change (s.map f).unop ≫ (s.map (homOfLE (Fin.zero_le i))).unop =
      (s.map (homOfLE (Fin.zero_le j))).unop
    rw [←unop_comp,←s.map_comp]
    congr 2)).op
  map_id i := by apply Quiver.Hom.unop_inj; apply Over.OverMorphism.ext; simp; rfl
  map_comp f g := by apply Quiver.Hom.unop_inj; apply Over.OverMorphism.ext; simp
lemma overLift_forget {n:ℕ} (s:Simplex C n) : overLift s ⋙ (Over.forget s.left.unop).op=s := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro source target arrow
  simp [overLift]
  change s.map arrow = 𝟙 _ ≫ s.map arrow
  exact (Category.id_comp _).symm
lemma overLift_map {n:ℕ} {x:C} (s:Simplex (Over x) n) :
    overLift (s ⋙ (Over.forget x).op) ⋙ (Over.map s.left.unop.hom).op=s := by
  apply CategoryTheory.Functor.ext
  · intro i j f
    apply Quiver.Hom.unop_inj
    apply Over.OverMorphism.ext
    simp
    change (s.map f).unop.left = 𝟙 _ ≫ (s.map f).unop.left ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]
  · intro i
    apply unop_injective
    refine Comma.ext (x:=(overLift (s ⋙ (Over.forget x).op) ⋙ (Over.map s.left.unop.hom).op).obj i|>.unop)
      (y:=(s.obj i).unop) rfl (Subsingleton.elim _ _) ?_
    apply heq_of_eq
    exact (s.map (homOfLE (Fin.zero_le i))).unop.w
noncomputable def overDiagram : C ⥤ SimplicialObject (ModuleCat.{0} R) where
  obj x := simplicial (Over.forget x ⋙ F)
  map {x y} f := post (Over.map f) (Over.forget y ⋙ F)
  map_id x := by
    apply NatTrans.ext; funext n
    apply hom_ext; intro s
    change single (Over.forget x ⋙ F) s ≫ desc _ _ = single (Over.forget x ⋙ F) s ≫ 𝟙 _
    erw [single_desc,Category.comp_id]
    have he : s ⋙ (Over.map (𝟙 x)).op=s := by rw [Over.mapId_eq]; rfl
    simpa only [eqToHom_refl,Category.id_comp] using! single_eq (Over.forget x ⋙ F) he rfl
  map_comp {x y z} f g := by
    apply NatTrans.ext; funext n
    apply hom_ext; intro s
    change single (Over.forget x ⋙ F) s ≫ desc _ _ =
      single (Over.forget x ⋙ F) s ≫ desc _ _ ≫ desc _ _
    erw [single_desc,single_desc_assoc,single_desc]
    have he : s ⋙ (Over.map (f ≫ g)).op=(s ⋙ (Over.map f).op) ⋙ (Over.map g).op := by
      rw [Over.mapComp_eq]; rfl
    simpa only [eqToHom_refl,Category.id_comp] using! single_eq (Over.forget z ⋙ F) he rfl
noncomputable def overCocone : Cocone (overDiagram F) where
  pt := simplicial F
  ι := { app x := post (Over.forget x) F
         naturality x y f := by
           apply NatTrans.ext; funext n
           apply hom_ext; intro s
           change single (Over.forget x ⋙ F) s ≫ desc _ _ ≫ desc _ _ =
             single (Over.forget x ⋙ F) s ≫ desc _ _
           erw [single_desc_assoc,single_desc,single_desc]
           rfl }
noncomputable def overPointwiseIsColimit (n:ℕ) :
    IsColimit (((evaluation _ (ModuleCat R)).obj (op ⦋n⦌)).mapCocone (overCocone F)) where
  desc d := desc F (fun s=>single (Over.forget s.left.unop ⋙ F) (overLift s) ≫ d.ι.app s.left.unop)
  fac d x := by
    apply hom_ext; intro s
    change single (Over.forget x ⋙ F) s ≫ desc _ _ ≫ desc _ _ = single (Over.forget x ⋙ F) s ≫ d.ι.app x
    erw [single_desc_assoc,single_desc]
    have h:=congrArg (fun k=>single (Over.forget s.left.unop.left ⋙ F) (overLift (s ⋙ (Over.forget x).op)) ≫ k) (d.w s.left.unop.hom)
    change _ = single _ _ ≫ d.ι.app s.left.unop.left at h
    change single (Over.forget s.left.unop.left ⋙ F) (overLift (s ⋙ (Over.forget x).op)) ≫
      d.ι.app s.left.unop.left=single (Over.forget x ⋙ F) s ≫ d.ι.app x
    rw [←h]
    change single (Over.forget s.left.unop.left ⋙ F) (overLift (s ⋙ (Over.forget x).op)) ≫
      desc _ _ ≫ d.ι.app x=single (Over.forget x ⋙ F) s ≫ d.ι.app x
    erw [single_desc_assoc]
    apply congrArg (fun z=>z ≫ d.ι.app x)
    simpa only [eqToHom_refl,Category.id_comp] using! single_eq (Over.forget x ⋙ F) (overLift_map s) rfl
  uniq d m hm := by
    apply hom_ext; intro s
    erw [single_desc]
    have h:=congrArg (fun k=>single (Over.forget s.left.unop ⋙ F) (overLift s) ≫ k) (hm s.left.unop)
    change single _ _ ≫ desc _ _ ≫ m=_ at h
    erw [single_desc_assoc] at h
    have he:=weighted_eq F (overLift_forget s) (𝟙 _) (𝟙 _) (by simp; rfl)
    simp only [CategoryTheory.Functor.map_id,Category.id_comp] at he
    change single F _ ≫ m = _ at h
    rw [he] at h
    erw [CategoryTheory.Functor.map_id, Category.id_comp] at h
    exact h
noncomputable def overIsColimit : IsColimit (overCocone F) :=
  evaluationJointlyReflectsColimits _ (fun n=>overPointwiseIsColimit F n.unop.len)
end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits Simplicial SimplicialObject Opposite AlgebraicTopology HomologicalComplex

variable {J C:Type} [Category.{0} J] [Category.{0} C]
noncomputable instance alternating_preserves :
    PreservesColimitsOfShape J (alternatingFaceMapComplex (ModuleCat.{0} ℤ)) := by
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro n
  change PreservesColimitsOfShape J ((evaluation SimplexCategoryᵒᵖ (ModuleCat.{0} ℤ)).obj (op ⦋n⦌))
  infer_instance
variable (F:C ⥤ ModuleCat.{0} ℤ)
lemma positive_acyclic [IsFiltered C] (n:ℕ) (hn:n≠0) : IsZero ((complex F).homology n) := by
  let H := alternatingFaceMapComplex (ModuleCat.{0} ℤ) ⋙ homologyFunctor _ (ComplexShape.down ℕ) n
  let h := isColimitOfPreserves H (overIsColimit F)
  apply (IsZero.iff_id_eq_zero _).mpr
  apply h.hom_ext
  intro x
  have hz : IsZero ((complex (Over.forget x ⋙ F)).homology n) := by
    apply IsZero.of_iso _ ((terminalHomotopyEquiv (Over.forget x ⋙ F)
      (d:=Over.mk (𝟙 x)) Over.mkIdTerminal).toHomologyIso n)
    apply ShortComplex.isZero_homology_of_isZero_X₂
    exact HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0 (F.obj x) n hn
  exact hz.eq_of_src _ _
end

end CoefficientNerve

end OAI
