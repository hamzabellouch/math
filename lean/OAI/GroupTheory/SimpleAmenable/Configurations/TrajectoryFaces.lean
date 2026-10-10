import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.TrajectoryReindexLabels

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory
namespace SimpleAmenable.PolygonObject.Labelled

variable {n : ℕ}
abbrev faceFunctor (i : Fin (n+2)) : Fin (n+1) ⥤ Fin (n+2) :=
  (SimplexCategory.δ i).toOrderHom.toFunctor
lemma faceFunctor_obj (i : Fin (n+2)) (k : Fin (n+1)) :
    (faceFunctor i).obj k = i.succAbove k := rfl
lemma reindexLabel_zero_face (g : Fin (n+1) → CutRing × CutRing) :
    reindexLabel (faceFunctor (0 : Fin (n+2))) g = Fin.tail g := by
  funext k
  simp only [reindexLabel,faceFunctor_obj,Fin.zero_succAbove,Fin.partialSum_succ']
  rw [show g 0 + Fin.partialSum (Fin.tail g) k.succ -
    (g 0 + Fin.partialSum (Fin.tail g) k.castSucc) =
    -Fin.partialSum (Fin.tail g) k.castSucc + Fin.partialSum (Fin.tail g) k.succ by abel]
  rw [Fin.partialSum_succ]
  abel
lemma reindexLabel_succ_face (g : Fin (n+1) → CutRing × CutRing) (i : Fin (n+1)) :
    reindexLabel (faceFunctor i.succ) g = i.contractNth (·+·) g := by
  funext k
  simp only [reindexLabel,faceFunctor_obj,Fin.succ_succAbove_succ]
  rw [sub_eq_add_neg,add_comm]
  exact Fin.neg_partialSum_add_eq_contractNth g i k
lemma initialDisplacement_zero_face (g : Fin (n+1) → CutRing × CutRing) :
    initialDisplacement (faceFunctor (0 : Fin (n+2))) g = g 0 := by
  simp only [initialDisplacement,faceFunctor_obj,Fin.zero_succAbove,Fin.partialSum_succ',Fin.partialSum_zero,add_zero]
lemma initialDisplacement_succ_face (g : Fin (n+1) → CutRing × CutRing) (i : Fin (n+1)) :
    initialDisplacement (faceFunctor i.succ) g = 0 := by
  simp only [initialDisplacement,faceFunctor_obj,Fin.succ_succAbove_zero,Fin.partialSum_zero]
end SimpleAmenable.PolygonObject.Labelled

end

end OAI
