import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.PointFiberHomology
import OAI.GroupTheory.SimpleAmenable.Configurations.CellRelabel

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Classical
namespace SimpleAmenable.PolygonObject.LabelledStage

variable {a n m : ℕ} {K : Type} [AddCommGroup K]
def labelMap (f : (Fin n → CutRing × CutRing) → (Fin m → CutRing × CutRing))
    (hf : ∀g,Labelled.Reduced g → Labelled.Reduced (f g)) : ReducedLabel n → ReducedLabel m :=
  fun l => ⟨f l.val,hf l.val l.property⟩
variable (f : (Fin n → CutRing × CutRing) → (Fin m → CutRing × CutRing))
  (hf : ∀g,Labelled.Reduced g → Labelled.Reduced (f g))
noncomputable def relabelCoefficients : Coefficients a n K →ₗ[ℤ] Coefficients a m K where
  toFun := Finsupp.mapDomain (labelMap f hf)
  map_add' _ _ := Finsupp.mapDomain_add
  map_smul' r x := by
    let h : Coefficients a n K →+ Coefficients a m K := {
      toFun := Finsupp.mapDomain (labelMap f hf)
      map_zero' := Finsupp.mapDomain_zero
      map_add' _ _ := Finsupp.mapDomain_add }
    exact map_intCast_smul h ℤ ℤ r x
@[simp] lemma relabelCoefficients_single (l : ReducedLabel n) (s : BooleanStep a K) :
    relabelCoefficients (a:=a) (K:=K) f hf (Finsupp.single l s)=Finsupp.single (labelMap f hf l) s :=
  Finsupp.mapDomain_single
end SimpleAmenable.PolygonObject.LabelledStage

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Classical
namespace SimpleAmenable.PolygonObject.LabelledStage.Stage
open IntervalBar.Diagram BarFinitePower FreeChains Labelled

variable {a n m : ℕ}
variable (f : (Fin n → CutRing × CutRing) → (Fin m → CutRing × CutRing))
  (hf : ∀g, Reduced g → Reduced (f g))
lemma homologyCoefficientIso_relabel (j : ℕ) (hj : 0<j) (hj5 : j≤5) :
    SSet.homologyMap (bar₃Map (relabel (a:=a) f hf)) Z j ≫
      (homologyCoefficientIso (a:=a) (n:=m) j hj hj5).hom =
    (homologyCoefficientIso (a:=a) (n:=n) j hj hj5).hom ≫
      ModuleCat.ofHom (relabelCoefficients (a:=a) (K:=K j) f hf) := by
  apply (cancel_epi (homologyCoefficientIso (a:=a) (n:=n) j hj hj5).inv).mp
  rw [Iso.inv_hom_id_assoc]
  apply ModuleCat.hom_ext
  apply LinearMap.toAddMonoidHom_injective
  apply Cell.coefficient_ext
  intro P l x
  have he := congrArg (fun k : K j ⟶ ModuleCat.of ℤ (Coefficients a n (K j)) => k x)
    (Cell.homology_coefficient P l j hj hj5)
  change (SSet.homologyMap (bar₃Map (Cell.functor P l)) Z j ≫
    (homologyCoefficientIso j hj hj5).hom) x = Finsupp.single l (Cell.step P x) at he
  change ((homologyCoefficientIso j hj hj5).inv ≫
    SSet.homologyMap (bar₃Map (relabel f hf)) Z j ≫ (homologyCoefficientIso j hj hj5).hom)
      (Finsupp.single l (Cell.step P x)) = _
  conv_lhs => rw [←he]
  change (SSet.homologyMap (bar₃Map (Cell.functor P l)) Z j ≫
    (homologyCoefficientIso j hj hj5).hom ≫ (homologyCoefficientIso j hj hj5).inv ≫
    SSet.homologyMap (bar₃Map (relabel f hf)) Z j ≫
    (homologyCoefficientIso j hj hj5).hom) x = _
  rw [Iso.hom_inv_id_assoc,←Category.assoc,←SSet.homologyMap_comp,←bar₃Map_comp,
    bar₃Map_eq_of_monoidalNatTrans (Cell.relabelIso f hf P l).hom j]
  erw [Cell.homology_coefficient P (labelMap f hf l) j hj hj5]
  exact (relabelCoefficients_single f hf l (Cell.step P x)).symm
end SimpleAmenable.PolygonObject.LabelledStage.Stage

end

end OAI
