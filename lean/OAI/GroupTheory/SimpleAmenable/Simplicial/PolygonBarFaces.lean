import Mathlib
import OAI.GroupTheory.SimpleAmenable.Configurations.PolygonStringNormalization

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PolygonBarFaces

open Classical CategoryTheory
namespace PolygonObject
variable {a n : ℕ}

@[simp] theorem deleteVertex_obj (j : Fin (n+2)) (i : Fin (n+1)) :
    (deleteVertex j).obj i=j.succAbove i := rfl

theorem increments_first_face (F : RawString a (n+1)) (x : (F.obj 0).Point) (i : Fin n) :
    increments (deleteVertex 0⋙F) ((baseArrow F ((deleteVertex 0).obj 0)).toEquiv x) i=
      increments F x i.succ := by
  apply increments_reindex_unchanged
  · simp only [deleteVertex_obj,Fin.zero_succAbove,Fin.castSucc_succ]
  · simp

theorem increments_last_face (F : RawString a (n+1)) (x : (F.obj 0).Point) (i : Fin n) :
    increments (deleteVertex (Fin.last (n+1))⋙F)
      ((baseArrow F ((deleteVertex (Fin.last (n+1))).obj 0)).toEquiv x) i=
      increments F x i.castSucc := by
  apply increments_reindex_unchanged
  · simp
  · simp only [deleteVertex_obj,Fin.succAbove_last_apply,Fin.castSucc_succ]

theorem increments_interior_face (F : RawString a (n+1)) (x : (F.obj 0).Point) (i : Fin n) :
    increments (deleteVertex i.succ.castSucc⋙F)
      ((baseArrow F ((deleteVertex i.succ.castSucc).obj 0)).toEquiv x) i=
      increments F x i.castSucc+increments F x i.succ := by
  apply increments_reindex_compose
  · change i.succ.castSucc.succAbove i.castSucc=i.castSucc.castSucc
    apply Fin.succAbove_of_castSucc_lt
    change i.val < i.val + 1
    omega
  · exact Fin.succ_castSucc i
  · simp

theorem first_face_initial_position (F : RawString a (n+1)) (x : (F.obj 0).Point) :
    ((baseArrow F ((deleteVertex (0 : Fin (n+2))).obj 0)).toEquiv x).val.2=
      translate a (increments F x 0) x.val.2 := by
  rw [pointShift_spec]
  congr 1
  change trajectoryShift F x ((deleteVertex 0).obj 0)=increments F x 0
  unfold increments
  simp only [deleteVertex_obj,Fin.zero_succAbove,Fin.castSucc_zero,trajectoryShift_zero,sub_zero]

theorem nonfirst_face_initial_position (F : RawString a (n+1)) (x : (F.obj 0).Point)
    (j : Fin (n+2)) (hj : j≠0) :
    ((baseArrow F ((deleteVertex j).obj 0)).toEquiv x).val.2=x.val.2 := by
  have he : (deleteVertex j).obj 0=0 := Fin.succAbove_ne_zero_zero hj
  rw [pointShift_spec]
  change translate a (trajectoryShift F x ((deleteVertex j).obj 0)) x.val.2=x.val.2
  rw [he,trajectoryShift_zero,translate_zero]

def duplicateVertex (j : Fin (n+1)) : Fin (n+2) ⥤ Fin (n+1) :=
  j.predAboveOrderHom.toFunctor

noncomputable def stringDegeneracy (j : Fin (n+1)) :
    StringGroupoid a n ⥤ StringGroupoid a (n+1) := stringReindex (duplicateVertex j)

@[simp] theorem duplicateVertex_obj (j : Fin (n+1)) (i : Fin (n+2)) :
    (duplicateVertex j).obj i=j.predAbove i := rfl

theorem increments_degeneracy (F : RawString a n) (x : (F.obj 0).Point) (j : Fin (n+1)) :
    increments (duplicateVertex j⋙F) ((baseArrow F ((duplicateVertex j).obj 0)).toEquiv x) j=0 := by
  apply increments_reindex_duplicate
  simp

end PolygonObject
end PolygonBarFaces

end SimpleAmenable
end
end

end OAI
