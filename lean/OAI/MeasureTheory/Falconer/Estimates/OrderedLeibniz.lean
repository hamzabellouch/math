import OAI.MeasureTheory.Falconer.Angular.AngularDifferentialExpr
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.List.Basic

namespace OAI

namespace PlanarFalconer
open scoped ContDiff

noncomputable def orderedDerivAssignments {ι : Type*} [DecidableEq ι]
    (S : Finset ι) : ℕ → List (ι → ℕ)
  | 0 => [fun _ => 0]
  | n+1 => (orderedDerivAssignments S n).flatMap
      (fun k => S.toList.map (fun i => Function.update k i (k i+1)))

theorem orderedDerivAssignments_length {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (n : ℕ) : (orderedDerivAssignments S n).length = S.card^n := by
  induction n with
  | zero => simp [orderedDerivAssignments]
  | succ n ih => simp [orderedDerivAssignments,List.length_flatMap,ih,pow_succ]

theorem orderedDerivAssignments_budget {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (n : ℕ) {k : ι → ℕ} (hk : k ∈ orderedDerivAssignments S n) :
    ∑ i ∈ S, k i = n := by
  induction n generalizing k with
  | zero => simp only [orderedDerivAssignments,List.mem_singleton] at hk; subst k; simp
  | succ n ih =>
    obtain ⟨l,hl,hk⟩ := List.mem_flatMap.mp hk
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hk
    have hi : i ∈ S := Finset.mem_toList.mp hi
    rw [Finset.sum_update_of_mem hi,Finset.sdiff_singleton_eq_erase]
    have he := Finset.add_sum_erase S l hi
    rw [ih hl] at he
    omega

noncomputable def assignedDerivProduct {ι : Type*} (S : Finset ι)
    (f : ι → ℝ → ℂ) (k : ι → ℕ) : ℝ → ℂ :=
  fun x => ∏ i ∈ S, iteratedDeriv (k i) (f i) x

theorem assignedDerivProduct_contDiff {ι : Type*} (S : Finset ι)
    (f : ι → ℝ → ℂ) (k : ι → ℕ) (hf : ∀ i ∈ S, ContDiff ℝ ∞ (f i)) :
    ContDiff ℝ ∞ (assignedDerivProduct S f k) :=
  contDiff_prod (fun i hi => AngularDifferentialExpr.smooth_iteratedDeriv (hf i hi) (k i))

theorem assignedDerivProduct_deriv {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (f : ι → ℝ → ℂ) (k : ι → ℕ) (hf : ∀ i ∈ S, ContDiff ℝ ∞ (f i)) (x : ℝ) :
    deriv (assignedDerivProduct S f k) x =
      ∑ i ∈ S, assignedDerivProduct S f (Function.update k i (k i+1)) x := by
  unfold assignedDerivProduct
  rw [deriv_fun_finsetProd (fun i hi =>
    (AngularDifferentialExpr.smooth_iteratedDeriv (hf i hi) _).differentiable (by simp) |>.differentiableAt)]
  apply Finset.sum_congr rfl
  intro i hi
  have he : (fun j => iteratedDeriv (Function.update k i (k i+1) j) (f j) x) =
      Function.update (fun j => iteratedDeriv (k j) (f j) x) i (iteratedDeriv (k i+1) (f i) x) := by
    funext j
    by_cases h : j = i <;> simp [h]
  rw [he,Finset.prod_update_of_mem hi]
  simp [iteratedDeriv_succ,smul_eq_mul,mul_comm,Finset.sdiff_singleton_eq_erase]

theorem contDiff_list_sum {α : Type*} (L : List α) (g : α → ℝ → ℂ)
    (hg : ∀ i ∈ L, ContDiff ℝ ∞ (g i)) :
    ContDiff ℝ ∞ (fun x => (L.map (fun i => g i x)).sum) := by
  induction L with
  | nil => simpa using (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => (0:ℂ)))
  | cons a L ih =>
    simpa using (hg a (by simp)).add (ih (fun i hi => hg i (by simp [hi])))

theorem deriv_list_sum {α : Type*} (L : List α) (g : α → ℝ → ℂ)
    (hg : ∀ i ∈ L, ContDiff ℝ ∞ (g i)) (x : ℝ) :
    deriv (fun x => (L.map (fun i => g i x)).sum) x =
      (L.map (fun i => deriv (g i) x)).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons,List.sum_cons]
    rw [deriv_fun_add ((hg a (by simp)).differentiable (by simp)).differentiableAt
      ((contDiff_list_sum L g (fun i hi => hg i (by simp [hi]))).differentiable (by simp)).differentiableAt]
    rw [ih (fun i hi => hg i (by simp [hi]))]

theorem iteratedDeriv_ordered_product {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f : ι → ℝ → ℂ) (hf : ∀ i ∈ S, ContDiff ℝ ∞ (f i)) (n : ℕ) :
    iteratedDeriv n (fun x => ∏ i ∈ S, f i x) =
      fun x => ((orderedDerivAssignments S n).map (fun k => assignedDerivProduct S f k x)).sum := by
  induction n with
  | zero => simp [orderedDerivAssignments,assignedDerivProduct]
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    funext x
    rw [deriv_list_sum _ _ (fun k _ => assignedDerivProduct_contDiff S f k hf)]
    simp only [orderedDerivAssignments,List.flatMap_def,List.map_flatten,List.sum_flatten,List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro k hk
    rw [assignedDerivProduct_deriv S f k hf]
    simp

end PlanarFalconer

end OAI
