import Mathlib
import OAI.GroupTheory.SimpleAmenable.RandomFields.PeriodizationCovariance
import OAI.GroupTheory.SimpleAmenable.Configurations.LabelledStringEquiv
import OAI.GroupTheory.SimpleAmenable.Simplicial.FinitePowerConnected
import OAI.GroupTheory.SimpleAmenable.Homology.StageCoefficients
import OAI.GroupTheory.SimpleAmenable.Simplicial.StageSimplicialColimit

namespace OAI

section

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace SimpleAmenable.PolygonObject.LabelledStage.Stage
open IntervalBar.Diagram BarFinitePower FreeChains

attribute [local instance 1200] Pi.module Prod.instModule
variable {a n:ℕ}
noncomputable abbrev E := bar₃ (C:=FiniteSetGroupoid)
lemma E_low_connected : LowConnected E := fun j hj h3 => bar₃_low_zero j hj h3
noncomputable abbrev K (j:ℕ) : ModuleCat ℤ := E.homology Z j
noncomputable def coefficientVectorIso (S:Stage a n) (j:ℕ) :
    ModuleCat.of ℤ (Fin S.partition.size × Fin S.support.card → K j) ≅
      (coefficientDiagram (a:=a) (n:=n) (K j)).obj S :=
  (AddEquiv.refl (Fin S.partition.size × Fin S.support.card → K j)).toIntLinearEquiv.toModuleIso
noncomputable def homologyCoordinates (S:Stage a n) (j:ℕ) :
    (bar₃ (C:=S.Obj)).homology Z j ⟶ (coefficientDiagram (a:=a) (n:=n) (K j)).obj S :=
  SSet.homologyMap S.finiteProductComparison Z j ≫ coordinates _ E j ≫ (S.coefficientVectorIso j).hom
lemma homologyCoordinates_isIso (S:Stage a n) (j:ℕ) (hj:0<j) (hj5:j≤5) :
    IsIso (S.homologyCoordinates j) := by
  have := S.finiteProductComparison_homology_isIso j
  have := coordinates_isIso_connected E E_low_connected (Fin S.partition.size × Fin S.support.card) j hj hj5
  unfold homologyCoordinates
  infer_instance
lemma homologyCoordinates_at (S:Stage a n) (j:ℕ)
    (x:((bar₃ (C:=S.Obj)).homology Z j : A)) (c:Fin S.partition.size × Fin S.support.card) :
    S.homologyCoordinates j x c =
      SSet.homologyMap (S.finiteProductComparison ≫ evaluate _ E c) Z j x := by
  rw [SSet.homologyMap_comp]
  rfl
lemma homologyCoordinates_refinement {S T:Stage a n} (h:S≤T) (j:ℕ) (hj:0<j) :
    SSet.homologyMap (bar₃Map (inclusion h)) Z j ≫ T.homologyCoordinates j =
      S.homologyCoordinates j ≫ (coefficientDiagram (a:=a) (n:=n) (K j)).map (homOfLE h) := by
  apply ModuleCat.hom_ext; apply LinearMap.ext; intro x; funext c
  change T.homologyCoordinates j (SSet.homologyMap (bar₃Map (inclusion h)) Z j x) c =
    (S.realize (K:=K j) (S.homologyCoordinates j x) (T.label c.2)).val (T.partition.point c.1)
  rw [homologyCoordinates_at]
  change (SSet.homologyMap (bar₃Map (inclusion h)) Z j ≫
    SSet.homologyMap (T.finiteProductComparison ≫ evaluate _ E c) Z j) x = _
  rw [←SSet.homologyMap_comp]
  by_cases hl:T.label c.2∈S.support
  · obtain ⟨b,hb⟩ := (S.label_range (T.label c.2)).mpr hl
    let d : Fin S.partition.size × Fin S.support.card := (S.partition.color (T.partition.point c.1),b)
    have hh : S.L b=T.L c.2 := congrArg Subtype.val hb
    rw [←refinement_coordinate h c d rfl hh j,←homologyCoordinates_at,←hb]
    erw [S.realize_at_label,BooleanStep.inflate_apply]
  · rw [refinement_new_label_zero h c (fun b hb => hl ((S.label_range (T.label c.2)).mp ⟨b,Subtype.ext hb⟩)) j hj]
    erw [S.realize_outside _ _ hl]
    rfl
noncomputable def homologyCoordinateIso (j:ℕ) (hj:0<j) (hj5:j≤5) :
    topRowsStage (a:=a) (n:=n) ⋙ SimplicialDiagonal.diagonal ⋙ SSet.homologyFunctor Z j ≅
      coefficientDiagram (a:=a) (n:=n) (K j) :=
  NatIso.ofComponents (fun S => by
    haveI := S.homologyCoordinates_isIso j hj hj5
    exact asIso (C := ModuleCat ℤ) (X := (bar₃ (C:=S.Obj)).homology Z j)
      (Y := (coefficientDiagram (a:=a) (n:=n) (K j)).obj S)
      (S.homologyCoordinates j)) (fun h => homologyCoordinates_refinement (leOfHom h) j hj)

noncomputable def homologyCoefficientIso (j:ℕ) (hj:0<j) (hj5:j≤5) :
    (bar₃ (C:=Labelled a n)).homology Z j ≅
      ModuleCat.of ℤ (Coefficients a n (K j)) :=
  (tripleBarHomologyIsColimit (a:=a) (n:=n) j).coconePointsIsoOfNatIso
    (coefficientIsColimit (a:=a) (n:=n) (K j)) (homologyCoordinateIso j hj hj5)
end SimpleAmenable.PolygonObject.LabelledStage.Stage

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory
open scoped TensorProduct
namespace SimpleAmenable.PolygonObject.LabelledStage

noncomputable def reducedLabelEquiv (n:ℕ) : ReducedLabel n ≃ (Fin n → Multiplicative (ℤ×ℤ)) where
  toFun l i := SquareStep.orbitProjection (Multiplicative.ofAdd (l.val i))
  invFun l := ⟨fun i => (SquareStep.orbitLift (l i)).toAdd,by
    intro i
    change orbitRepresentative (((l i).toAdd.1:CutRing)*cutTau,((l i).toAdd.2:CutRing)*cutTau)=_
    simp [orbitRepresentative,cutTau]
    rfl⟩
  left_inv l := by
    apply Subtype.ext; funext i
    exact l.property i
  right_inv l := by
    funext i
    change Multiplicative.ofAdd ((((l i).toAdd.1:CutRing)*cutTau).im,
      (((l i).toAdd.2:CutRing)*cutTau).im) = l i
    simp [cutTau]

noncomputable def trajectoryCoefficientEquiv (a n:ℕ) (K:Type) [AddCommGroup K] :
    Coefficients a n K ≃ₗ[ℤ]
      ((Fin n → Multiplicative (ℤ×ℤ)) →₀ (SquareStep a ⊗[ℤ] K)) :=
  (Finsupp.mapRange.linearEquiv (BooleanStep.tensorEquiv (a:=a) (K:=K)).symm).trans
    (Finsupp.domLCongr (reducedLabelEquiv n))
end SimpleAmenable.PolygonObject.LabelledStage

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory
open scoped TensorProduct
namespace SimpleAmenable.PolygonObject
open IntervalBar.Diagram LabelledStage FreeChains

noncomputable def trajectoryHomologyIso (a p j:ℕ) (hj:0<j) (hj5:j≤5) :
    (bar₃ (C:=StringGroupoid a p)).homology Z j ≅
      ModuleCat.of ℤ ((Fin p → Multiplicative (ℤ×ℤ)) →₀
        (SquareStep a ⊗[ℤ] Stage.K j)) := by
  haveI := Labelled.tripleBar_homology_isIso (a:=a) (n:=p) j
  refine (asIso (SSet.homologyMap (bar₃Map (Labelled.toStrings (a:=a) (n:=p))) Z j)).symm ≪≫
    Stage.homologyCoefficientIso j hj hj5 ≪≫ ?_
  let e := (trajectoryCoefficientEquiv a p (Stage.K j)).toModuleIso
  convert e using 2
  congr 4 <;> apply Subsingleton.elim
lemma trajectoryRows_low_zero (a p j:ℕ) (hj:0<j) (hj3:j<3) :
    IsZero ((bar₃ (C:=StringGroupoid a p)).homology Z j) :=
  bar₃_low_zero j hj hj3
end SimpleAmenable.PolygonObject

end

end

end OAI
