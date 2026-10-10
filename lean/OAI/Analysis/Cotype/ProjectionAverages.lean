import OAI.Analysis.Cotype.ProjectionDeficit

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def projectionChoiceCons (Ω : Type*) (n : ℕ) :
    Ω × (Fin n → Ω) ≃ (Fin (n+1) → Ω) where
  toFun p := Fin.cons p.1 p.2
  invFun u := (u 0, Fin.tail u)
  left_inv p := by ext i <;> simp
  right_inv u := by ext i; exact Fin.cases (by simp) (fun i => by simp; rfl) i

theorem projectionProduct_weighted_sum {Ω : Type*} [Fintype Ω] {n : ℕ}
    (w : Fin n → Ω → ℝ) (P : Fin n → Ω → X →L[ℝ] X) :
    projectionProduct (fun i => ∑ a, w i a • P i a) =
      ∑ ω : Fin n → Ω, (∏ i, w i (ω i)) • projectionProduct (fun i => P i (ω i)) := by
  classical
  induction n with
  | zero => simp [projectionProduct]
  | succ n ih =>
    rw [← (projectionChoiceCons Ω n).sum_comp]
    simp only [Fintype.sum_prod_type, projectionChoiceCons, Equiv.coe_fn_mk,
      Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, projectionProduct]
    rw [ih]
    simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
      Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro ω _
    rw [mul_comm]

theorem projectionProduct_const (T : X →L[ℝ] X) (n : ℕ) :
    projectionProduct (fun _ : Fin n => T) = T^n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [projectionProduct, ih, pow_succ']

theorem projection_weight_total {Ω : Type*} [Fintype Ω] {n : ℕ}
    (w : Fin n → Ω → ℝ) (hw : ∀ i, ∑ a, w i a = 1) :
    (∑ ω : Fin n → Ω, ∏ i, w i (ω i)) = 1 := by
  rw [← Fintype.prod_sum]
  simp_rw [hw]
  simp

theorem averaged_projection_power_bound_of_sign_deficit {n : ℕ} (hn : 0 < n) {δ : ℝ}
    (h : ∀ x : Fin n → X, (∀ i, ‖x i‖ ≤ 1) →
      ∃ ε : Cube n, ‖rademacherSum X x ε‖ ≤ (n : ℝ)-δ)
    {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (hw : ∀ a, 0 ≤ w a) (hw1 : ∑ a, w a = 1)
    (P : Ω → X →L[ℝ] X)
    (hp : ∀ a, P a * P a = P a) (hc : ∀ a b, Commute (P a) (P b))
    (hP : ∀ a x, ‖P a x‖ ≤ ‖x‖) (y : X) :
    ‖((1-∑ a, w a • P a)^n) y‖ ≤ ((2 : ℝ)^n-δ/n)*‖y‖ := by
  classical
  have he : (1-∑ a, w a • P a) = ∑ a, w a • (1-P a) := by
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hw1, one_smul]
  rw [he, ← projectionProduct_const, projectionProduct_weighted_sum]
  simp only [sum_apply, smul_apply]
  calc
    _ ≤ ∑ ω : Fin n → Ω, ‖(∏ i, w (ω i)) • projectionProduct (fun i => 1-P (ω i)) y‖ :=
      norm_sum_le _ _
    _ ≤ ∑ ω : Fin n → Ω, (∏ i, w (ω i))*(((2 : ℝ)^n-δ/n)*‖y‖) := by
      apply Finset.sum_le_sum
      intro ω _
      have hwω : 0 ≤ ∏ i : Fin n, w (ω i) := Finset.prod_nonneg (fun i _ => hw (ω i))
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hwω]
      apply mul_le_mul_of_nonneg_left _ hwω
      exact projection_complement_bound_of_sign_deficit hn h (fun i => P (ω i))
        (fun i => hp (ω i)) (fun i j => hc (ω i) (ω j)) (fun i => hP (ω i)) y
    _ = _ := by rw [← Finset.sum_mul, projection_weight_total (fun _ => w) (fun _ => hw1), one_mul]

end Cotype

end

end OAI
