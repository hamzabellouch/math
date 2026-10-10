import OAI.Probability.ClassicalON.DyadicModes

namespace OAI

universe uP uX

noncomputable section
open scoped BigOperators ComplexConjugate

namespace ClassicalON

def SquareBound {X : Type uX} {P : Type uP} [Fintype X] [Fintype P]
    (U : X → P → ℂ) (a : ℝ) : Prop :=
  ∀ v : P → ℂ, (∑ x, ‖∑ p, U x p*v p‖^2) ≤ a^2*∑ p, ‖v p‖^2

variable {X : Type uX} {P : Type uP} [Fintype X] [Fintype P]

theorem SquareBound.column {U : X → P → ℂ} {a : ℝ} (h : SquareBound U a) (p : P) :
    ∑ x, ‖U x p‖^2 ≤ a^2 := by
  classical
  have hs : (∑ q : P, ‖((Pi.single p (1:ℂ)) : P → ℂ) q‖^2) = 1 := by
    simp only [Pi.single_apply, apply_ite, norm_one, norm_zero, ite_pow, one_pow,
      zero_pow (by decide : 2 ≠ 0), Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have he := h (Pi.single p 1)
  rw [hs, mul_one] at he
  simpa only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] using he

theorem SquareBound.gram_weighted {U : X → P → ℂ} {a : ℝ}
    (h : SquareBound U a) (d : P → ℂ) :
    (∑ x, ∑ y, ‖∑ p, U x p*d p*conj (U y p)‖^2) ≤ a^4*∑ p, ‖d p‖^2 := by
  calc _ = ∑ y, ∑ x, ‖∑ p, U x p*(d p*conj (U y p))‖^2 := by
          simp only [mul_assoc]
          exact Finset.sum_comm
       _ ≤ ∑ y, a^2*∑ p, ‖d p*conj (U y p)‖^2 :=
          Finset.sum_le_sum fun y _ => h (fun p => d p*conj (U y p))
       _ = a^2*∑ p, ‖d p‖^2*(∑ y, ‖U y p‖^2) := by
          simp only [norm_mul, Complex.norm_conj, mul_pow, Finset.mul_sum]
          rw [Finset.sum_comm]
       _ ≤ a^2*∑ p, ‖d p‖^2*a^2 := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
          exact Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_left (h.column p) (sq_nonneg _)
       _ = _ := by rw [← Finset.sum_mul]; ring

theorem sum_norm_add_sq_le (f g : X → ℂ) :
    (∑ x, ‖f x+g x‖^2) ≤ 2*(∑ x, ‖f x‖^2)+2*(∑ x, ‖g x‖^2) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  have hv := norm_add_le (f x) (g x)
  have hsq := sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _)) |>.mpr hv
  nlinarith [sq_nonneg (‖f x‖-‖g x‖)]

theorem parseval_of_orthogonal [DecidableEq P] (W : X → P → ℂ) (M : ℝ)
    (ho : ∀ p q, (∑ x, W x p*conj (W x q)) = if p=q then (M:ℂ) else 0)
    (v : P → ℂ) :
    (∑ x, ‖∑ p, W x p*v p‖^2) = M*∑ p, ‖v p‖^2 := by
  classical
  have he : (∑ x, (∑ p, W x p*v p)*conj (∑ q, W x q*v q)) =
      (M:ℂ)*∑ p, v p*conj (v p) := by
    simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    calc
      (∑ x, ∑ q, ∑ p, W x p*v p*(conj (W x q)*conj (v q))) =
          ∑ q, ∑ p, ∑ x, W x p*v p*(conj (W x q)*conj (v q)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun q _ => Finset.sum_comm)
      _ = ∑ p, ∑ q, (∑ x, W x p*conj (W x q))*(v p*conj (v q)) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro p _
        apply Finset.sum_congr rfl
        intro q _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = _ := by simp [ho]
  have hr := congrArg Complex.re he
  simp only [Complex.mul_conj, Complex.normSq_eq_norm_sq,
    Complex.ofReal_re, ← Complex.ofReal_sum, ← Complex.ofReal_mul] at hr
  exact hr

theorem parseval_diagonal_bound [DecidableEq P] (W : X → P → ℂ) (M c : ℝ) (hM : 0 ≤ M)
    (ho : ∀ p q, (∑ x, W x p*conj (W x q)) = if p=q then (M:ℂ) else 0)
    (d v : P → ℂ) (hd : ∀ p, ‖d p‖ ≤ c) :
    (∑ x, ‖∑ p, W x p*(d p*v p)‖^2) ≤ (M*c^2)*∑ p, ‖v p‖^2 := by
  rw [parseval_of_orthogonal W M ho, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hM
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p _
  rw [norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hd p) 2) (sq_nonneg _)

end ClassicalON

end

end OAI
