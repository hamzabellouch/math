import Mathlib

namespace OAI

section
noncomputable section
open scoped BigOperators

namespace SharpTerminalLeave

theorem moving_perturbation_finite_expansion {X : Type*} [AddCommGroup X] [Module ℝ X]
    (V : Module.End ℝ X) (x y : X) (h : x = y + V x) (K : ℕ) :
    x = (∑ j ∈ Finset.range K, (V^j) y) + (V^K) x := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, pow_succ]
    calc
      x = (∑ j ∈ Finset.range K, (V^j) y) + (V^K) x := ih
      _ = (∑ j ∈ Finset.range K, (V^j) y) + (V^K) (y + V x) := by rw [← h]
      _ = _ := by simp [Module.End.mul_apply, add_assoc]

lemma seminorm_end_pow_le {X : Type*} [AddCommGroup X] [Module ℝ X]
    (p : Seminorm ℝ X) (V : Module.End ℝ X) {A : ℝ} (hA : 0 ≤ A)
    (hV : ∀ x, p (V x) ≤ A * p x) (K : ℕ) (x : X) :
    p ((V^K) x) ≤ A^K * p x := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [pow_succ',Module.End.mul_apply,pow_succ']
    exact (hV _).trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left ih hA)

lemma seminorm_finset_sum_le {X I : Type*} [AddCommGroup X] [Module ℝ X]
    (p : Seminorm ℝ X) (s : Finset I) (f : I → X) :
    p (∑ i ∈ s, f i) ≤ ∑ i ∈ s, p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (map_add_le_add p _ _).trans (add_le_add le_rfl ih)

theorem moving_perturbation_mixed_norm_bound {X : Type*} [AddCommGroup X] [Module ℝ X]
    (p q : Seminorm ℝ X) (V : Module.End ℝ X) (x y : X)
    {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hVp : ∀ z, p (V z) ≤ A * p z) (hVq : ∀ z, q (V z) ≤ B * q z)
    (hpq : ∀ z, p z ≤ q z) (hqp : ∀ z, q z ≤ C * p z)
    (h : x = y + V x) (K : ℕ) :
    p x ≤ (∑ j ∈ Finset.range K, A^j) * p y + B^K * C * p x := by
  have he := moving_perturbation_finite_expansion V x y h K
  calc
    p x = p ((∑ j ∈ Finset.range K, (V^j) y) + (V^K) x) := congrArg p he
    _ ≤ p (∑ j ∈ Finset.range K, (V^j) y) + p ((V^K) x) := map_add_le_add p _ _
    _ ≤ (∑ j ∈ Finset.range K, p ((V^j) y)) + q ((V^K) x) :=
      add_le_add (seminorm_finset_sum_le p _ _) (hpq _)
    _ ≤ (∑ j ∈ Finset.range K, A^j * p y) + B^K * q x :=
      add_le_add (Finset.sum_le_sum (fun j _ => seminorm_end_pow_le p V hA hVp j y))
        (seminorm_end_pow_le q V hB hVq K x)
    _ ≤ (∑ j ∈ Finset.range K, A^j * p y) + B^K * (C * p x) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (hqp x) (pow_nonneg hB K))
    _ = _ := by rw [Finset.sum_mul]; ring

theorem moving_perturbation_mixed_norm_absorb {X : Type*} [AddCommGroup X] [Module ℝ X]
    (p q : Seminorm ℝ X) (V : Module.End ℝ X) (x y : X)
    {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hVp : ∀ z, p (V z) ≤ A * p z) (hVq : ∀ z, q (V z) ≤ B * q z)
    (hpq : ∀ z, p z ≤ q z) (hqp : ∀ z, q z ≤ C * p z)
    (h : x = y + V x) (K : ℕ) (hK : B^K*C ≤ 1/2) :
    p x ≤ 2*(∑ j ∈ Finset.range K, A^j)*p y := by
  have hb := moving_perturbation_mixed_norm_bound p q V x y hA hB hVp hVq hpq hqp h K
  have hp : 0 ≤ p x := apply_nonneg p x
  have ht := mul_le_mul_of_nonneg_right hK hp
  nlinarith only [hb,ht]

theorem moving_perturbation_mixed_norm_absorb_modulo {X : Type*} [AddCommGroup X] [Module ℝ X]
    (p q : Seminorm ℝ X) (V : Module.End ℝ X) (x y : X)
    {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hVp : ∀ z, p (V z) ≤ A * p z) (hVq : ∀ z, q (V z) ≤ B * q z)
    (hpq : ∀ z, p z ≤ q z) (hqp : ∀ z, q z ≤ C * p z)
    (h : p (x-y-V x) = 0) (K : ℕ) (hK : B^K*C ≤ 1/2) :
    p x ≤ 2*(∑ j ∈ Finset.range K, A^j)*p y := by
  let z := x-y-V x
  have he : x = (y+z)+V x := by dsimp only [z]; abel
  have hb := moving_perturbation_mixed_norm_absorb p q V x (y+z) hA hB hVp hVq hpq hqp he K hK
  have hy : p (y+z) ≤ p y := by
    have hh := map_add_le_add p y z
    change p z = 0 at h
    linarith only [hh,h]
  apply hb.trans
  exact mul_le_mul_of_nonneg_left hy (by positivity)

end SharpTerminalLeave
end
end

end OAI
