import OAI.Analysis.Cotype.ProjectionSemigroupBasics

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

def projectionPattern {m : ℕ} (P : Fin m → Y →L[ℝ] Y) (ε : Cube m) : Y →L[ℝ] Y :=
  projectionProduct (fun i => if ε i then 1-P i else P i)

theorem projectionProduct_pointwise_mul {m : ℕ} (P Q : Fin m → Y →L[ℝ] Y)
    (hc : ∀ i j, Commute (P i) (Q j)) :
    projectionProduct P * projectionProduct Q = projectionProduct (fun i => P i * Q i) := by
  induction m with
  | zero => simp [projectionProduct]
  | succ m ih =>
    have hm := projectionProduct_commute (fun i => P i.succ) (Q 0)
      (fun i => hc i.succ 0)
    have ht := ih (fun i => P i.succ) (fun i => Q i.succ)
      (fun i j => hc i.succ j.succ)
    simp only [projectionProduct]
    rw [mul_assoc, ← mul_assoc (projectionProduct _), hm.eq, mul_assoc, ht, ← mul_assoc]

theorem projectionProduct_zero_of_factor {m : ℕ} (P : Fin m → Y →L[ℝ] Y)
    (i : Fin m) (hi : P i = 0) : projectionProduct P = 0 := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    refine Fin.cases ?_ (fun j => ?_) i hi
    · intro h
      simp [projectionProduct, h]
    · intro h
      simp only [projectionProduct]
      rw [ih (fun j => P j.succ) j h, mul_zero]

theorem projectionPattern_factor_commute (P Q : Y →L[ℝ] Y)
    (h : Commute P Q) (b c : Bool) :
    Commute (if b then 1-P else P) (if c then 1-Q else Q) := by
  have h1 : Commute P (1-Q) := (Commute.one_right P).sub_right h
  have h2 : Commute (1-P) Q := (Commute.one_left Q).sub_left h
  have h3 : Commute (1-P) (1-Q) := (Commute.one_right _).sub_right h2
  cases b <;> cases c
  · exact h
  · exact h1
  · exact h2
  · exact h3

theorem projectionPattern_mul {m : ℕ} (P : Fin m → Y →L[ℝ] Y)
    (hp : ∀ i, P i * P i = P i) (hc : ∀ i j, Commute (P i) (P j))
    (ε η : Cube m) :
    projectionPattern P ε * projectionPattern P η =
      if ε = η then projectionPattern P ε else 0 := by
  classical
  unfold projectionPattern
  rw [projectionProduct_pointwise_mul _ _
    (fun i j => projectionPattern_factor_commute _ _ (hc i j) _ _)]
  by_cases he : ε = η
  · subst η
    rw [ite_eq_left rfl]
    congr 1
    funext i
    cases ε i
    · exact hp i
    · simp only [ite_true, sub_mul, mul_sub, one_mul, mul_one, hp i]
      abel
  · rw [ite_eq_right he]
    obtain ⟨i, hi⟩ : ∃ i, ε i ≠ η i := by
      by_contra! h
      exact he (funext h)
    apply projectionProduct_zero_of_factor _ i
    cases hε : ε i <;> cases hη : η i <;> simp_all [sub_mul, mul_sub]

theorem projectionPattern_sum {m : ℕ} (P : Fin m → Y →L[ℝ] Y) :
    (∑ ε : Cube m, projectionPattern P ε) = 1 := by
  have h := projectionProduct_weighted_sum (fun (_ : Fin m) (_ : Bool) => (1 : ℝ))
    (fun i (b : Bool) => if b then 1-P i else P i)
  simpa [Fintype.sum_bool, projectionPattern, projectionProduct_one] using h.symm

theorem projectionSemigroup_pattern_expansion {m : ℕ} (P : Fin m → Y →L[ℝ] Y) (r : ℝ) :
    projectionSemigroup P r =
      ∑ ε : Cube m, (∏ i, if ε i then r else 1) • projectionPattern P ε := by
  have h := projectionProduct_weighted_sum
    (fun (_ : Fin m) (b : Bool) => if b then r else 1)
    (fun i (b : Bool) => if b then 1-P i else P i)
  simpa [Fintype.sum_bool, projectionSemigroup, projectionPattern, add_comm] using h

end Cotype

end

end OAI
