import OAI.MeasureTheory.Falconer.Angular.AngularOperatorTerms
import Mathlib.Algebra.Order.BigOperators.Group.List

namespace OAI

namespace PlanarFalconer
open scoped ContDiff

noncomputable def inverseLeibnizTerms {ι : Type*} [DecidableEq ι] (j : ℕ) (S : Finset ι) :
    List (ℂ × (ι → ℕ)) :=
  (inverseStationaryExpr j).terms.flatMap (fun a =>
    (orderedDerivAssignments S a.2).map (fun k => (a.1,k)))

theorem inverseLeibnizTerms_budget {ι : Type*} [DecidableEq ι] (j : ℕ) (S : Finset ι)
    {a : ℂ × (ι → ℕ)} (ha : a ∈ inverseLeibnizTerms j S) :
    ∑ i ∈ S, a.2 i ≤ 2*j := by
  obtain ⟨b,hb,ha⟩ := List.mem_flatMap.mp ha
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp ha
  rw [orderedDerivAssignments_budget S b.2 hk]
  exact inverseStationaryOperator_terms_order j hb

theorem inverseLeibnizTerms_expansion {ι : Type*} [DecidableEq ι] (j : ℕ) (S : Finset ι)
    (f : ι → ℝ → ℂ) (hf : ∀ i ∈ S, ContDiff ℝ ∞ (f i)) (x : ℝ) :
    inverseStationaryOperator j (fun x => ∏ i ∈ S, f i x) x =
      ((inverseLeibnizTerms j S).map (fun a => a.1*assignedDerivProduct S f a.2 x)).sum := by
  rw [inverseStationaryOperator_terms j (contDiff_prod hf)]
  simp only [inverseLeibnizTerms,List.flatMap_def,List.map_flatten,List.sum_flatten,List.map_map,
    Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  rw [iteratedDeriv_ordered_product S f hf a.2]
  exact (List.sum_map_mul_left _ _ _).symm

theorem inverseLeibnizTerms_length {ι : Type*} [DecidableEq ι] (j : ℕ) (S : Finset ι) :
    (inverseLeibnizTerms j S).length ≤
      (inverseStationaryExpr j).terms.length * (max 1 S.card)^(2*j) := by
  simp only [inverseLeibnizTerms,List.length_flatMap,List.length_map,orderedDerivAssignments_length]
  calc
    _ ≤ (((inverseStationaryExpr j).terms).map (fun _ => (max 1 S.card)^(2*j))).sum := by
      apply List.sum_le_sum
      intro a ha
      exact (Nat.pow_le_pow_left (le_max_right 1 S.card) a.2).trans
        (Nat.pow_le_pow_right (by omega) (inverseStationaryOperator_terms_order j ha))
    _ = _ := by simp

theorem inverseLeibnizTerms_cost {ι : Type*} [DecidableEq ι] (j : ℕ) (S : Finset ι) :
    ((inverseLeibnizTerms j S).map (fun a => ‖a.1‖)).sum ≤
      (inverseStationaryExpr j).cost * (max 1 (S.card:ℝ))^(2*j) := by
  simp only [inverseLeibnizTerms,List.flatMap_def,List.map_flatten,List.sum_flatten,List.map_map,
    Function.comp_def]
  calc
    _ ≤ ((inverseStationaryExpr j).terms.map
        (fun a => ‖a.1‖*(max 1 (S.card:ℝ))^(2*j))).sum := by
      apply List.sum_le_sum
      intro a ha
      simp only [List.map_const',List.sum_replicate,orderedDerivAssignments_length,nsmul_eq_mul,
        Nat.cast_pow]
      rw [mul_comm]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact (pow_le_pow_left₀ (Nat.cast_nonneg _) (le_max_right 1 (S.card:ℝ)) a.2).trans
        (pow_le_pow_right₀ (le_max_left _ _) (inverseStationaryOperator_terms_order j ha))
    _ = _ := by rw [List.sum_map_mul_right,AngularDifferentialExpr.terms_cost]

end PlanarFalconer

end OAI
