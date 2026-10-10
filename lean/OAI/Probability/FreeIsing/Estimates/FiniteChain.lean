import Mathlib

namespace OAI

namespace Problem367.FiniteChain

variable {A : Type*}

def weight (K : A → A → ℝ) : (n : ℕ) → A → (Fin n → A) → ℝ
  | 0, _, _ => 1
  | n + 1, a, x => K a (x 0) * weight K n (x 0) (Fin.tail x)

def endpoint : (n : ℕ) → A → (Fin n → A) → A
  | 0, a, _ => a
  | n + 1, _, x => endpoint n (x 0) (Fin.tail x)

@[simp] theorem weight_zero (K : A → A → ℝ) (a : A) (x : Fin 0 → A) :
    weight K 0 a x = 1 := rfl

@[simp] theorem endpoint_zero (a : A) (x : Fin 0 → A) :
    endpoint 0 a x = a := rfl

@[simp] theorem weight_cons (K : A → A → ℝ) (n : ℕ) (a b : A) (x : Fin n → A) :
    weight K (n + 1) a (Fin.cons b x) = K a b * weight K n b x := by
  simp [weight]

@[simp] theorem endpoint_cons (n : ℕ) (a b : A) (x : Fin n → A) :
    endpoint (n + 1) a (Fin.cons b x) = endpoint n b x := by
  simp [endpoint]

theorem weight_eq_prod (K : A → A → ℝ) (n : ℕ) (a : A) (x : Fin n → A) :
    weight K n a x = ∏ i : Fin n, K ((Fin.cons a x : Fin (n+1) → A) i.castSucc) (x i) := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [weight, Fin.prod_univ_succ, ih]
    simp [Fin.tail]

theorem endpoint_eq_last (n : ℕ) (a : A) (x : Fin n → A) :
    endpoint n a x = (Fin.cons a x : Fin (n+1) → A) (Fin.last n) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    rw [endpoint, ih]
    simp

theorem weight_nonneg (K : A → A → ℝ) (hK : ∀ a b, 0 ≤ K a b)
    (n : ℕ) (a : A) (x : Fin n → A) : 0 ≤ weight K n a x := by
  induction n generalizing a with
  | zero => simp
  | succ n ih => exact mul_nonneg (hK _ _) (ih _ _)

variable [Fintype A]

theorem sum_cons (n : ℕ) (f : (Fin (n+1) → A) → ℝ) :
    ∑ x, f x = ∑ a, ∑ x : Fin n → A, f (Fin.cons a x) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => A)).sum_comp f]
  rw [Fintype.sum_prod_type]
  rfl

def expectation (K : A → A → ℝ) (n : ℕ) (f : A → ℝ) (a : A) : ℝ :=
  ∑ x : Fin n → A, weight K n a x * f (endpoint n a x)

@[simp] theorem expectation_zero (K : A → A → ℝ) (f : A → ℝ) (a : A) :
    expectation K 0 f a = f a := by
  simp [expectation]

theorem expectation_succ (K : A → A → ℝ) (n : ℕ) (f : A → ℝ) (a : A) :
    expectation K (n+1) f a = ∑ b, K a b * expectation K n f b := by
  unfold expectation
  rw [sum_cons]
  simp only [weight_cons, endpoint_cons, mul_assoc, Finset.mul_sum]

theorem expectation_eigenfunction (K : A → A → ℝ) (f : A → ℝ) (r : ℝ)
    (hf : ∀ a, ∑ b, K a b * f b = r * f a) (n : ℕ) (a : A) :
    expectation K n f a = r^n * f a := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [expectation_succ]
    simp_rw [ih]
    calc
      ∑ b, K a b * (r ^ n * f b) = r ^ n * ∑ b, K a b * f b := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b hb
        ring
      _ = r ^ (n+1) * f a := by rw [hf, pow_succ]; ring

theorem sum_weight (K : A → A → ℝ) (hK : ∀ a, ∑ b, K a b = 1)
    (n : ℕ) (a : A) : ∑ x : Fin n → A, weight K n a x = 1 := by
  have h := expectation_eigenfunction K (fun _ => 1) 1 (by simpa using hK) n a
  simpa [expectation] using h

end Problem367.FiniteChain

end OAI
