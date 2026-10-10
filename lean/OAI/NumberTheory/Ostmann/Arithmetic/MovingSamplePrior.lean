import OAI.NumberTheory.Ostmann.Arithmetic.MovingSampleValues
import OAI.NumberTheory.Ostmann.Construction.FiniteEnumeration

namespace OAI

/-! # The original independent compensation samples

Section 7.4, equations (7.10)--(7.11), samples one compensation vector at
each node. That vector is shared by its two children; samples subsequently
made in the children are independent. These are the literal finite priors,
before any distinctness or equality-pattern restriction.
-/

namespace Ostmann
open scoped Classical BigOperators

def movingSampleNodeEquiv (A : Type*) (n : ℕ) :
    TreeLeafTuple (Fin 4 → A) n × MovingSampleSlots A n × MovingSampleSlots A n ≃
      MovingSampleSlots A (n + 1) where
  toFun x := .node x.1 x.2.1 x.2.2
  invFun x := match x with | .node a l r => (a, l, r)
  left_inv _ := rfl
  right_inv x := by cases x; rfl

def movingSampleZeroEquiv (A : Type*) : Unit ≃ MovingSampleSlots A 0 where
  toFun _ := .leaf
  invFun _ := ()
  left_inv _ := rfl
  right_inv x := by cases x; rfl

noncomputable instance movingSampleSlotsFintype (A : Type*) [Fintype A] :
    (n : ℕ) → Fintype (MovingSampleSlots A n)
  | 0 => Fintype.ofEquiv Unit (movingSampleZeroEquiv A)
  | n + 1 => @Fintype.ofEquiv _ _
      (@instFintypeProd _ _ (treeLeafTupleFintype (Fin 4 → A) n)
        (@instFintypeProd _ _ (movingSampleSlotsFintype A n) (movingSampleSlotsFintype A n)))
      (movingSampleNodeEquiv A n)

noncomputable def movingCompensationPrior {A : Type*} (μ : A → ℝ) :
    (n : ℕ) → TreeLeafTuple (Fin 4 → A) n → ℝ
  | 0, a => ∏ i : Fin 4, μ (a i)
  | n + 1, a => movingCompensationPrior μ n a.1 * movingCompensationPrior μ n a.2

noncomputable def movingSamplesPrior {A : Type*} (μ : ℕ → A → ℝ) :
    {n : ℕ} → MovingSampleSlots A n → ℝ
  | _, .leaf => 1
  | n + 1, .node a l r =>
      movingCompensationPrior (μ n) n a * movingSamplesPrior μ l * movingSamplesPrior μ r

theorem movingCompensationPrior_nonneg {A : Type*} (μ : A → ℝ)
    (hμ : ∀ a, 0 ≤ μ a) (n : ℕ) (a : TreeLeafTuple (Fin 4 → A) n) :
    0 ≤ movingCompensationPrior μ n a := by
  induction n with
  | zero => exact Finset.prod_nonneg (fun i _ => hμ (a i))
  | succ n ih => exact mul_nonneg (ih a.1) (ih a.2)

theorem movingSamplesPrior_nonneg {A : Type*} (μ : ℕ → A → ℝ)
    (hμ : ∀ n a, 0 ≤ μ n a) {n : ℕ} (a : MovingSampleSlots A n) :
    0 ≤ movingSamplesPrior μ a := by
  induction a with
  | leaf => exact zero_le_one
  | node a l r hl hr =>
      exact mul_nonneg (mul_nonneg (movingCompensationPrior_nonneg _ (hμ _) _ a) hl) hr

theorem movingCompensationPrior_mass {A : Type*} [Fintype A] (μ : A → ℝ)
    (hμ : ∑ a, μ a = 1) (n : ℕ) :
    ∑ a : TreeLeafTuple (Fin 4 → A) n, movingCompensationPrior μ n a = 1 := by
  induction n with
  | zero =>
      change (∑ a : Fin 4 → A, ∏ i : Fin 4, μ (a i)) = 1
      rw [← Fintype.prod_sum]
      simp only [hμ, Finset.prod_const_one]
  | succ n ih =>
      change (∑ a : TreeLeafTuple (Fin 4 → A) n × TreeLeafTuple (Fin 4 → A) n,
        movingCompensationPrior μ n a.1 * movingCompensationPrior μ n a.2) = 1
      rw [Fintype.sum_prod_type, ← Finset.sum_mul_sum, ih, one_mul]

theorem sum_movingSample_node {A M : Type*} [Fintype A] [AddCommMonoid M]
    (n : ℕ) (f : MovingSampleSlots A (n + 1) → M) :
    (∑ a, f a) = ∑ u : TreeLeafTuple (Fin 4 → A) n,
      ∑ l : MovingSampleSlots A n, ∑ r : MovingSampleSlots A n, f (.node u l r) := by
  have h := (movingSampleNodeEquiv A n).sum_comp f
  simp only [finite_univ_canonical] at h ⊢
  rw [← h]
  have h₁ := Fintype.sum_prod_type (fun x : TreeLeafTuple (Fin 4 → A) n ×
      MovingSampleSlots A n × MovingSampleSlots A n => f ((movingSampleNodeEquiv A n) x))
  simp only [finite_univ_canonical] at h₁
  rw [h₁]
  apply Finset.sum_congr rfl
  intro u _
  have h₂ := Fintype.sum_prod_type (fun x : MovingSampleSlots A n × MovingSampleSlots A n =>
    f (.node u x.1 x.2))
  simp only [finite_univ_canonical] at h₂
  refine Eq.trans ?_ h₂
  apply Finset.sum_congr rfl
  intro x _
  rfl

theorem movingSamplesPrior_mass {A : Type*} [Fintype A] (μ : ℕ → A → ℝ)
    (hμ : ∀ n, ∑ a, μ n a = 1) (n : ℕ) :
    ∑ a : MovingSampleSlots A n, movingSamplesPrior μ a = 1 := by
  induction n with
  | zero =>
      have h := (movingSampleZeroEquiv A).sum_comp (movingSamplesPrior μ)
      simpa only [movingSampleZeroEquiv, Equiv.coe_fn_mk, movingSamplesPrior,
        Finset.univ_unique, Finset.sum_singleton] using h.symm
  | succ n ih =>
      rw [sum_movingSample_node]
      simp only [movingSamplesPrior, ← Finset.mul_sum, ih, mul_one,
        movingCompensationPrior_mass _ (hμ n)]

/-- Independent descendants factor, while the single root vector is retained
outside both child expectations. No prime-distinctness event is conditioned on. -/
theorem movingSamplesPrior_node_product {A : Type*} [Fintype A]
    (μ : ℕ → A → ℝ) (n : ℕ)
    (c : TreeLeafTuple (Fin 4 → A) n → ℂ)
    (L R : TreeLeafTuple (Fin 4 → A) n → MovingSampleSlots A n → ℂ) :
    (∑ a : MovingSampleSlots A (n + 1), (movingSamplesPrior μ a : ℂ) *
      (match a with | .node u l r => c u * L u l * star (R u r))) =
      ∑ u : TreeLeafTuple (Fin 4 → A) n, (movingCompensationPrior (μ n) n u : ℂ) * c u *
        (∑ l : MovingSampleSlots A n, (movingSamplesPrior μ l : ℂ) * L u l) *
          star (∑ r : MovingSampleSlots A n, (movingSamplesPrior μ r : ℂ) * R u r) := by
  rw [sum_movingSample_node]
  apply Finset.sum_congr rfl
  intro u _
  simp only [movingSamplesPrior, Complex.ofReal_mul, star_sum, star_mul,
    Complex.star_def, Complex.conj_ofReal, Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro r _
  ring

end Ostmann

end OAI
