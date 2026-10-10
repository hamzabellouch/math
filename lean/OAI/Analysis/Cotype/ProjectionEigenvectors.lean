import OAI.Analysis.Cotype.ProjectionSemigroup

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem projectionProduct_eigenvector {n : ℕ} (P : Fin n → X →L[ℝ] X)
    (c : Fin n → ℝ) (x : X) (h : ∀ i, P i x = c i • x) :
    projectionProduct P x = (∏ i, c i) • x := by
  induction n with
  | zero => simp [projectionProduct]
  | succ n ih =>
    change P 0 (projectionProduct (fun i => P i.succ) x) = _
    rw [ih _ _ (fun i => h i.succ), map_smul, h 0, smul_smul, Fin.prod_univ_succ, mul_comm]

theorem projectionSubset_eigenvector {n : ℕ} (P : Fin n → X →L[ℝ] X)
    (c : Fin n → ℝ) (x : X) (h : ∀ i, P i x = c i • x) (ε : Cube n) :
    projectionSubset P ε x = (∏ i, if ε i then c i else 1) • x := by
  apply projectionProduct_eigenvector
  intro i
  cases ε i <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  · simp
  · exact h i

theorem projectionLinearCoefficient_eigenvector {n : ℕ} (P : Fin n → X →L[ℝ] X)
    (p : Cube n) (x : X) (h : ∀ i, P i x = (if p i then (0 : ℝ) else 1) • x) :
    projectionLinearCoefficient P x = ∑ i : Fin n, if p = unitIndex i then x else 0 := by
  classical
  have he i : (1-P i) (projectionSubset P (fun j => decide (j ≠ i)) x) =
      if p = unitIndex i then x else 0 := by
    rw [projectionSubset_eigenvector P _ x h]
    simp only [map_smul, sub_apply, one_apply_eq_self, h]
    by_cases hi : p i = true
    · simp only [hi, ite_true, zero_smul, sub_zero]
      by_cases hall : ∀ j, j ≠ i → p j = false
      · have hp : p = unitIndex i := by
          funext j
          by_cases hj : j=i
          · subst j; simp [unitIndex, hi]
          · simp [hall j hj, unitIndex, Ne.symm hj]
        rw [ite_eq_left hp]
        have hprod : (∏ j, if decide (j ≠ i) then (if p j then (0 : ℝ) else 1) else 1) = 1 := by
          apply Finset.prod_eq_one
          intro j _
          by_cases hj : j=i
          · simp [hj]
          · simp [hj, hall j hj]
        rw [hprod, one_smul]
      · push Not at hall
        obtain ⟨j,hji,hpj⟩ := hall
        have hpj' : p j = true := by cases hq : p j <;> simp_all
        have hprod : (∏ j, if decide (j ≠ i) then (if p j then (0 : ℝ) else 1) else 1) = 0 := by
          apply Finset.prod_eq_zero (Finset.mem_univ j)
          simp [hji,hpj']
        have hne : p ≠ unitIndex i := by
          intro hh
          have := congrFun hh j
          simp [unitIndex, Ne.symm hji, hpj'] at this
        rw [hprod, zero_smul, ite_eq_right hne]
    · have hip : p i = false := by cases hq : p i <;> simp_all
      have hne : p ≠ unitIndex i := by
        intro hh
        have := congrFun hh i
        simp [unitIndex,hip] at this
      simp [hip,hne]
  simp only [projectionLinearCoefficient, sum_apply]
  exact Finset.sum_congr rfl (fun i _ => he i)

end Cotype

end

end OAI
