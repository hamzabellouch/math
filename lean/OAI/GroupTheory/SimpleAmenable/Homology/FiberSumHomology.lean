import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.StageHomologyCoordinates
import OAI.GroupTheory.SimpleAmenable.Configurations.FiberAddition

namespace OAI

section

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory
namespace SimpleAmenable.PolygonObject.FiniteSetGroupoid
open BarFiberProduct IntervalBar.Diagram BarFinitePower FreeChains
open LabelledStage.Stage

attribute [local instance 1200] Pi.module Prod.instModule
noncomputable def fiberCoordinates (j:ℕ) :
    (bar₃ (C:=Bool→FiniteSetGroupoid)).homology Z j ⟶ ModuleCat.of ℤ (Bool→K j) :=
  SSet.homologyMap (triplePowerComparison Bool) Z j ≫ coordinates Bool E j
lemma fiberCoordinates_isIso (j:ℕ) (hj:0<j) (h5:j≤5) : IsIso (fiberCoordinates j) := by
  have := triplePowerComparison_homology_isIso (C:=FiniteSetGroupoid) Bool j
  have := coordinates_isIso_connected E E_low_connected Bool j hj h5
  unfold fiberCoordinates
  infer_instance
lemma fiberCoordinates_at (j:ℕ) (x:((bar₃ (C:=Bool→FiniteSetGroupoid)).homology Z j:A)) (k:Bool) :
    fiberCoordinates j x k = SSet.homologyMap (bar₃Map (project Bool k)) Z j x := by
  change (SSet.homologyMap (triplePowerComparison Bool) Z j ≫
    SSet.homologyMap (evaluate Bool E k) Z j) x = _
  rw [←SSet.homologyMap_comp]
  rfl
lemma fiberCoordinates_insert (b k:Bool) (j:ℕ) (hj:0<j) (x:K j) :
    fiberCoordinates j (SSet.homologyMap (bar₃Map (insertFiber b)) Z j x) k =
      if b=k then x else 0 := by
  rw [fiberCoordinates_at]
  change (SSet.homologyMap (bar₃Map (insertFiber b)) Z j ≫
    SSet.homologyMap (bar₃Map (project Bool k)) Z j) x = _
  rw [←SSet.homologyMap_comp,←bar₃Map_comp,
    bar₃Map_eq_of_monoidalNatTrans (insertCoordinate b k).hom j,selected_homology b k j hj]
  split <;> rfl
lemma merge_insert_homology (b:Bool) (j:ℕ) (x:K j) :
    SSet.homologyMap (bar₃Map merge) Z j
      (SSet.homologyMap (bar₃Map (insertFiber b)) Z j x) = x := by
  change (SSet.homologyMap (bar₃Map (insertFiber b)) Z j ≫
    SSet.homologyMap (bar₃Map merge) Z j) x = _
  rw [←SSet.homologyMap_comp,←bar₃Map_comp,
    bar₃Map_eq_of_monoidalNatTrans (mergeInsertIso b).hom j,bar₃Map_id_homology]
  rfl

lemma merge_homology_addition (j:ℕ) (hj:0<j) (h5:j≤5)
    (x:((bar₃ (C:=Bool→FiniteSetGroupoid)).homology Z j:A)) :
    SSet.homologyMap (bar₃Map merge) Z j x =
      fiberCoordinates j x false + fiberCoordinates j x true := by
  have := fiberCoordinates_isIso j hj h5
  have hx : x =
      SSet.homologyMap (bar₃Map (insertFiber false)) Z j (fiberCoordinates j x false) +
      SSet.homologyMap (bar₃Map (insertFiber true)) Z j (fiberCoordinates j x true) := by
    apply (ModuleCat.mono_iff_injective (fiberCoordinates j)).mp inferInstance
    rw [map_add]
    funext k
    cases k <;> simp [fiberCoordinates_insert _ _ j hj]
  rw [hx,map_add,merge_insert_homology,merge_insert_homology]
  simp only [map_add,Pi.add_apply,fiberCoordinates_insert _ _ j hj]
  simp
end SimpleAmenable.PolygonObject.FiniteSetGroupoid

end

end

end OAI
