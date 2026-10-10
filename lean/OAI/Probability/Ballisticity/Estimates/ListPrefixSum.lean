import Mathlib
import OAI.Probability.Ballisticity.Estimates.IidListProcess

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma realPartialSum_list {G : Type*} (F : G → ℝ) (c : ℝ) (w : List G) {k : ℕ} (hk : k ≤ w.length) :
    realPartialSum (fun j => if h : j < w.length then F (w.get ⟨j,h⟩)-c else 0) k =
      ((w.take k).map F).sum-(k:ℝ)*c := by
  induction k with
  | zero => simp [realPartialSum]
  | succ k ih =>
    rw [realPartialSum_succ,ih (by omega)]
    have hkl : k < w.length := by omega
    rw [dite_eq_left hkl]
    rw [List.take_add_one,List.getElem?_eq_getElem hkl]
    simp only [List.get_eq_getElem,Option.toList_some,List.map_append,List.sum_append,List.map_singleton,List.sum_singleton,Nat.cast_add,Nat.cast_one]
    ring

lemma signedCoordinate_list_sum {d : ℕ} (f : Direction d) (w : List (Lattice d)) :
    (w.map (signedCoordinate f)).sum=signedCoordinate f w.sum := by
  induction w with
  | nil => simp [signedCoordinate]
  | cons u w ih => simp only [List.map_cons,List.sum_cons,signedCoordinate_add,ih]

lemma listCenteredMax_prefix {d : ℕ} (f : Direction d) (c : ℝ) (w : List (Lattice d))
    {k : ℕ} (hk : k ≤ w.length) :
    |signedCoordinate f (w.take k).sum-(k:ℝ)*c| ≤ listCenteredMax (signedCoordinate f) c w := by
  rw [← signedCoordinate_list_sum]
  rw [← realPartialSum_list _ c w hk]
  exact (abs_partialSum_le_max _ k).trans (partialSumMax_mono _ hk)

end DirectionalTransience

end

end

end OAI
