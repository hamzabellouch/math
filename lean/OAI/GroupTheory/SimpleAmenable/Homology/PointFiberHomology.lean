import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.StageHomologyCoordinates
import OAI.GroupTheory.SimpleAmenable.Configurations.FiberAddition
import OAI.GroupTheory.SimpleAmenable.Configurations.CellFiber

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory
namespace SimpleAmenable.PolygonObject.LabelledStage
open IntervalBar.Diagram BarFinitePower FreeChains

variable {a n : ℕ} {K : Type} [AddCommGroup K]
variable {modK : Module ℤ K}
noncomputable def pointValue (c : GenericSquare a × ReducedLabel n) :
    Coefficients a n K →ₗ[ℤ] K where
  toFun f := (f c.2).val c.1
  map_add' _ _ := rfl
  map_smul' r f := by
    let h : Coefficients a n K →+ K := {
      toFun f := (f c.2).val c.1
      map_zero' := rfl
      map_add' _ _ := rfl }
    exact map_intCast_smul h ℤ ℤ r f
namespace Stage
variable (S : Stage a n)
lemma homologyCoefficientIso_stage (j : ℕ) (hj : 0<j) (hj5 : j≤5) :
    SSet.homologyMap (bar₃Map S.forget) Z j ≫ (homologyCoefficientIso (a:=a) (n:=n) j hj hj5).hom =
      S.homologyCoordinates j ≫ ModuleCat.ofHom (S.realize (K:=Stage.K j)) :=
  IsColimit.comp_coconePointsIsoOfNatIso_hom
    (tripleBarHomologyIsColimit j) (coefficientIsColimit (Stage.K j))
    (homologyCoordinateIso j hj hj5) S
lemma homologyCoefficientIso_point (j : ℕ) (hj : 0<j) (hj5 : j≤5)
    (c : GenericSquare a × ReducedLabel n) :
    (homologyCoefficientIso (a:=a) (n:=n) j hj hj5).hom ≫
      ModuleCat.ofHom (pointValue (K:=Stage.K j) c) =
    SSet.homologyMap (bar₃Map (Labelled.PointFiber.evaluation ⋙ project _ (c.1,c.2.val))) Z j := by
  apply (tripleBarHomologyIsColimit (a:=a) (n:=n) j).hom_ext
  intro S
  change SSet.homologyMap (bar₃Map S.forget) Z j ≫
      ((homologyCoefficientIso j hj hj5).hom ≫ ModuleCat.ofHom (pointValue c)) =
    SSet.homologyMap (bar₃Map S.forget) Z j ≫
      SSet.homologyMap (bar₃Map (Labelled.PointFiber.evaluation ⋙ project _ (c.1,c.2.val))) Z j
  rw [←Category.assoc,homologyCoefficientIso_stage,←SSet.homologyMap_comp,←bar₃Map_comp]
  by_cases hc : c.2∈S.support
  · obtain ⟨k,hk⟩ := (S.label_range c.2).mpr hc
    let b : Fin S.partition.size × Fin S.support.card := (S.partition.color c.1,k)
    have hl : S.L b.2 = c.2.val := congrArg Subtype.val hk
    rw [←bar₃Map_eq_of_monoidalNatTrans
      (pointEvaluationIso S b (c.1,c.2.val) rfl hl).hom j]
    apply ModuleCat.hom_ext; apply LinearMap.ext; intro x
    change (S.realize (K:=Stage.K j) (S.homologyCoordinates j x) c.2).val c.1 = _
    rw [←hk]
    erw [S.realize_at_label,BooleanStep.inflate_apply]
    rw [←S.finiteProductComparison_coordinate b,←S.homologyCoordinates_at]
  · rw [←bar₃Map_eq_of_monoidalNatTrans
      (emptyPointIso (c.1,c.2.val) (fun k hk => hc
        ((S.label_range c.2).mp ⟨k,Subtype.ext hk⟩))).hom j,
      bar₃Map_comp,SSet.homologyMap_comp]
    have hz := bar₃_acyclic (C:=FiniteSetGroupoid.Terminal)
      (fun x y => ⟨eqToHom (Subsingleton.elim x y)⟩) j hj
    rw [hz.eq_of_src (SSet.homologyMap (bar₃Map FiniteSetGroupoid.emptyFunctor) Z j) 0,comp_zero]
    apply ModuleCat.hom_ext; apply LinearMap.ext; intro x
    change (S.realize (K:=Stage.K j) (S.homologyCoordinates j x) c.2).val c.1 = 0
    erw [S.realize_outside _ _ hc]
    rfl
end Stage
end SimpleAmenable.PolygonObject.LabelledStage

end

namespace SimpleAmenable.PolygonObject.Labelled.Cell
section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Classical

variable {a n : ℕ} {K : Type} [AddCommGroup K]
noncomputable def step (P : polygonAlgebra a) (x : K) : BooleanStep a K :=
  ⟨fun p => if p∈P.val then x else 0,by
    obtain ⟨S,hS⟩ := polygon_hasSquareArrangement P.property
    refine ⟨S,fun p q h => ?_⟩
    have hh := decide_eq_decide.mp (hS p q h)
    simp only [hh]⟩
@[simp] lemma step_apply (P : polygonAlgebra a) (x : K) (p : GenericSquare a) :
    (step P x).val p=if p∈P.val then x else 0 := rfl
@[simp] lemma step_zero (P : polygonAlgebra a) : step P (0:K)=0 := by
  apply Subtype.ext; funext p; simp [step]
@[simp] lemma step_add (P : polygonAlgebra a) (x y : K) : step P (x+y)=step P x+step P y := by
  apply Subtype.ext; funext p
  change (if p∈P.val then x+y else 0) =
    (if p∈P.val then x else 0)+(if p∈P.val then y else 0)
  split_ifs <;> simp
variable {modK : Module ℤ K}
noncomputable def coefficient (P : polygonAlgebra a) (l : LabelledStage.ReducedLabel n) :
    K →ₗ[ℤ] LabelledStage.Coefficients a n K where
  toFun x := Finsupp.single l (step P x)
  map_add' _ _ := by rw [step_add,Finsupp.single_add]
  map_smul' r x := by
    let h : K →+ LabelledStage.Coefficients a n K := {
      toFun x := Finsupp.single l (step P x)
      map_zero' := by rw [step_zero,Finsupp.single_zero]
      map_add' _ _ := by rw [step_add,Finsupp.single_add] }
    exact map_intCast_smul h ℤ ℤ r x
@[simp] lemma coefficient_apply (P : polygonAlgebra a) (l : LabelledStage.ReducedLabel n) (x : K) :
    coefficient (K:=K) (modK:=modK) P l x=Finsupp.single l (step P x) := rfl

lemma coefficient_ext {T : Type} [AddCommGroup T] {f g : LabelledStage.Coefficients a n K →+ T}
    (h : ∀P l x,f (Finsupp.single l (step P x))=g (Finsupp.single l (step P x))) : f=g := by
  apply AddMonoidHom.ext; intro v
  induction v using Finsupp.induction with
  | zero => simp only [map_zero]
  | @single_add l s v hl hs ih =>
    rw [map_add,map_add,ih]
    congr 1
    obtain ⟨Q,hQ⟩ := BooleanStep.exists_common (fun _ : Unit => s)
    have hsQ := hQ ()
    have he : s = ∑i:Fin Q.size,step ⟨_,Q.polygon i⟩ ((s.val) (Q.point i)) := by
      apply Subtype.ext; funext p
      have hv := congrArg (fun w : BooleanStep a K => w.val p) hsQ
      change (BooleanStep.inflate (K:=K) Q (BooleanStep.evaluate (K:=K) Q s)).val p=s.val p at hv
      rw [BooleanStep.inflate_apply,BooleanStep.evaluate_apply] at hv
      rw [←hv]
      rw [Submodule.coe_sum,Finset.sum_apply]
      simp only [step,Set.mem_ofPred_eq]
      rw [Finset.sum_eq_single (Q.color p)]
      · simp
      · intro index _ hindex
        simp [Ne.symm hindex]
      · simp
    rw [he,Finsupp.single_finsetSum,map_sum,map_sum]
    apply Finset.sum_congr rfl; intro i _; exact h _ _ _
end

open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Classical
open IntervalBar.Diagram BarFinitePower FreeChains LabelledStage

variable {a n : ℕ} (P : polygonAlgebra a) (l : ReducedLabel n)
lemma homology_point (j : ℕ) (hj : 0<j)
    (c : GenericSquare a × ReducedLabel n) :
    SSet.homologyMap (bar₃Map (functor P l ⋙ PointFiber.evaluation ⋙ project _ (c.1,c.2.val))) Z j =
      if c.1∈P.val ∧ l=c.2 then 𝟙 _ else 0 := by
  split_ifs with h
  · rw [←bar₃Map_eq_of_monoidalNatTrans
      (evaluationIso P l (c.1,c.2.val) h.1 (congrArg Subtype.val h.2)).hom j]
    exact bar₃Map_id_homology j
  · rw [←bar₃Map_eq_of_monoidalNatTrans
      (emptyIso P l (c.1,c.2.val) (fun hh => h ⟨hh.1,Subtype.ext hh.2⟩)).hom j,
      bar₃Map_comp,SSet.homologyMap_comp]
    have hz := bar₃_acyclic (C:=FiniteSetGroupoid.Terminal)
      (fun x y => ⟨eqToHom (Subsingleton.elim x y)⟩) j hj
    rw [hz.eq_of_src (SSet.homologyMap (bar₃Map FiniteSetGroupoid.emptyFunctor) Z j) 0,comp_zero]
lemma homology_coefficient (j : ℕ) (hj : 0<j) (hj5 : j≤5) :
    SSet.homologyMap (bar₃Map (functor P l)) Z j ≫
      (Stage.homologyCoefficientIso (a:=a) (n:=n) j hj hj5).hom =
    ModuleCat.ofHom (coefficient (K:=Stage.K j) P l) := by
  apply ModuleCat.hom_ext; apply LinearMap.ext; intro x
  apply Finsupp.ext; intro k
  apply Subtype.ext; funext p
  have h := congrArg (fun f : Stage.K j ⟶ Stage.K j => f x)
    (congrArg (fun f => SSet.homologyMap (bar₃Map (functor P l)) Z j ≫ f)
      (Stage.homologyCoefficientIso_point (a:=a) (n:=n) j hj hj5 (p,k)))
  rw [←SSet.homologyMap_comp,←bar₃Map_comp,homology_point P l j hj (p,k)] at h
  change _ = (Finsupp.single l (step P x) k).val p
  refine h.trans ?_
  by_cases hl:l=k
  · subst k
    simp only [and_true,Finsupp.single_eq_same,step_apply]
    split_ifs <;> rfl
  · simp only [hl,and_false,ite_false,Finsupp.single_eq_of_ne (Ne.symm hl)]
    rfl
end SimpleAmenable.PolygonObject.Labelled.Cell

end OAI
