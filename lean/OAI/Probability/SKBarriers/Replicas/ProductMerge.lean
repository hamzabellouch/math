import Mathlib
import OAI.Probability.SKBarriers.Replicas.VectorBranch

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic
section Vector
variable {E F : Type}

def mergedProductBranches (l : List (ℝ × E)) (r : List (ℝ × F)) : List (ProductIncrement (E:=E) (F:=F)) :=
  (l.map Sum.inl).merge (r.map Sum.inr) (fun p q => decide (productMass p ≤ productMass q))

theorem mergedProductBranches_left (l : List (ℝ × E)) (r : List (ℝ × F)) :
    productLeft (mergedProductBranches l r)=l := by
  induction l generalizing r with
  | nil => simp [mergedProductBranches,productLeft,List.filterMap_map]
  | cons p l ih =>
    induction r with
    | nil => simp [mergedProductBranches,productLeft,List.filterMap_map]
    | cons q r ihr =>
      unfold mergedProductBranches
      simp only [List.map_cons,List.cons_merge_cons]
      split
      · simp only [productLeft,List.filterMap_cons]
        exact congrArg (List.cons p) (ih (q::r))
      · simp only [productLeft,List.filterMap_cons]
        exact ihr

theorem mergedProductBranches_right (l : List (ℝ × E)) (r : List (ℝ × F)) :
    productRight (mergedProductBranches l r)=r := by
  induction l generalizing r with
  | nil => simp [mergedProductBranches,productRight,List.filterMap_map]
  | cons p l ih =>
    induction r with
    | nil => simp [mergedProductBranches,productRight,List.filterMap_map]
    | cons q r ihr =>
      unfold mergedProductBranches
      simp only [List.map_cons,List.cons_merge_cons]
      split
      · simp only [productRight,List.filterMap_cons]
        exact ih (q::r)
      · simp only [productRight,List.filterMap_cons]
        exact congrArg (List.cons q) ihr

theorem mergedProductBranches_monotone (l : List (ℝ × E)) (r : List (ℝ × F))
    (hl : l.Pairwise (fun p q => p.1 ≤ q.1))
    (hr : r.Pairwise (fun p q => p.1 ≤ q.1)) :
    (mergedProductBranches l r).Pairwise (fun p q => productMass p ≤ productMass q) := by
  unfold mergedProductBranches
  have hl' : (l.map (Sum.inl : (ℝ × E) → (ProductIncrement (E:=E) (F:=F)))).Pairwise
      (fun p q => productMass p ≤ productMass q) := by simpa [List.pairwise_map,productMass] using hl
  have hr' : (r.map (Sum.inr : (ℝ × F) → (ProductIncrement (E:=E) (F:=F)))).Pairwise
      (fun p q => productMass p ≤ productMass q) := by
    rw [List.pairwise_map]
    exact hr.imp (fun h => div_le_div_of_nonneg_right h (by norm_num))
  have ht : ∀ a b c : (ProductIncrement (E:=E) (F:=F)),
      decide (productMass a ≤ productMass b) = true →
      decide (productMass b ≤ productMass c) = true →
      decide (productMass a ≤ productMass c) = true := by
    intro a b c hab hbc
    simp only [decide_eq_true_eq] at hab hbc ⊢
    exact le_trans hab hbc
  have htot : ∀ a b : (ProductIncrement (E:=E) (F:=F)),
      (decide (productMass a ≤ productMass b) || decide (productMass b ≤ productMass a)) = true := by
    intro a b
    simp only [Bool.or_eq_true,decide_eq_true_eq]
    exact le_total _ _
  simpa only [decide_eq_true_eq] using List.pairwise_merge ht htot
    _ _ (by simpa only [decide_eq_true_eq] using hl') (by simpa only [decide_eq_true_eq] using hr')

end Vector
end SK.Analytic

end
end

end OAI
