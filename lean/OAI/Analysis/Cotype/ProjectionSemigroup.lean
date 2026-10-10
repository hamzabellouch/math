import OAI.Analysis.Cotype.ProjectionAverages

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def projectionSemigroup {m : ℕ} (P : Fin m → X →L[ℝ] X) (r : ℝ) : X →L[ℝ] X :=
  projectionProduct (fun i => P i + r • (1-P i))

def projectionWeight {m : ℕ} (r : ℝ) (ε : Cube m) : ℝ :=
  ∏ i, if ε i then 1-r else r

def projectionLinearCoefficient {m : ℕ} (P : Fin m → X →L[ℝ] X) : X →L[ℝ] X :=
  ∑ i, (1-P i) * projectionSubset P (fun j => decide (j ≠ i))

theorem projectionSemigroup_average {m : ℕ} (P : Fin m → X →L[ℝ] X) (r : ℝ) :
    projectionSemigroup P r = ∑ ε : Cube m, projectionWeight r ε • projectionSubset P ε := by
  have he i : (∑ b : Bool, (if b then 1-r else r) • (if b then P i else 1)) =
      P i+r • (1-P i) := by
    simp only [Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false]
    module
  unfold projectionSemigroup
  simp_rw [← he]
  exact projectionProduct_weighted_sum _ _

theorem projectionWeight_nonneg {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    {m : ℕ} (ε : Cube m) : 0 ≤ projectionWeight r ε := by
  apply Finset.prod_nonneg
  intro i _
  cases ε i <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  · exact hr
  · linarith

theorem projectionWeight_sum (r : ℝ) (m : ℕ) :
    (∑ ε : Cube m, projectionWeight r ε) = 1 := by
  unfold projectionWeight
  apply projection_weight_total (fun (_ : Fin m) (b : Bool) => if b then 1-r else r)
  intro i
  simp only [Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false]
  ring

theorem projectionSubset_idempotent {m : ℕ} (P : Fin m → X →L[ℝ] X)
    (hp : ∀ i, P i * P i = P i) (hc : ∀ i j, Commute (P i) (P j)) (ε : Cube m) :
    projectionSubset P ε * projectionSubset P ε = projectionSubset P ε := by
  simpa using projectionSubset_union P hp hc ε ε

theorem projectionSubset_pairwise_commute {m : ℕ} (P : Fin m → X →L[ℝ] X)
    (hp : ∀ i, P i * P i = P i) (hc : ∀ i j, Commute (P i) (P j)) (ε η : Cube m) :
    Commute (projectionSubset P ε) (projectionSubset P η) := by
  show _ * _ = _ * _
  rw [projectionSubset_union P hp hc, projectionSubset_union P hp hc]
  congr 1
  funext i
  exact Bool.or_comm _ _

theorem projectionSemigroup_power_bound_of_sign_deficit {n : ℕ} (hn : 0 < n) {δ : ℝ}
    (h : ∀ x : Fin n → X, (∀ i, ‖x i‖ ≤ 1) →
      ∃ ε : Cube n, ‖rademacherSum X x ε‖ ≤ (n : ℝ)-δ)
    {m : ℕ} (P : Fin m → X →L[ℝ] X)
    (hp : ∀ i, P i * P i = P i) (hc : ∀ i j, Commute (P i) (P j))
    (hP : ∀ i x, ‖P i x‖ ≤ ‖x‖) {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) (y : X) :
    ‖((1-projectionSemigroup P r)^n) y‖ ≤ ((2 : ℝ)^n-δ/n)*‖y‖ := by
  rw [projectionSemigroup_average]
  exact averaged_projection_power_bound_of_sign_deficit hn h (projectionWeight r)
    (projectionWeight_nonneg hr hr1) (projectionWeight_sum r m) (projectionSubset P)
    (projectionSubset_idempotent P hp hc) (projectionSubset_pairwise_commute P hp hc)
    (projectionSubset_norm_apply P hP) y

theorem projectionSemigroup_power_gap_of_bConvex (h : BConvex X) :
    ∃ n : ℕ, 0 < n ∧ ∃ C : ℝ, 0 ≤ C ∧ C < (2 : ℝ)^n ∧
      ∀ (m : ℕ) (P : Fin m → X →L[ℝ] X),
        (∀ i, P i * P i = P i) → (∀ i j, Commute (P i) (P j)) →
        (∀ i x, ‖P i x‖ ≤ ‖x‖) → ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
        ∀ y : X, ‖((1-projectionSemigroup P r)^n) y‖ ≤ C*‖y‖ := by
  obtain ⟨n,hn,δ,hδ,h⟩ := h
  let C : ℝ := max 0 ((2 : ℝ)^n-δ/n)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨n,hn,C,le_max_left _ _,?_,fun m P hp hc hP r hr hr1 y => ?_⟩
  · exact max_lt (by positivity) (sub_lt_self _ (div_pos hδ hnR))
  · exact (projectionSemigroup_power_bound_of_sign_deficit hn h P hp hc hP hr hr1 y).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg y))

end Cotype

end

end OAI
