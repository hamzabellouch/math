import OAI.Probability.FreeIsing.Estimates.InhomogeneousSpinChain

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem367.InhomogeneousChain

variable {A : Type*} [Fintype A]

def advance (K : ℕ → A → A → ℝ) (w : A → ℝ) (b : A) : ℝ :=
  ∑ a, w a * K 0 a b

def coordinateMean (K : ℕ → A → A → ℝ) (w f : A → ℝ)
    (n : ℕ) (i : Fin (n + 1)) : ℝ :=
  ∑ x : Fin (n + 1) → A, jointWeight K w n x * f (x i)

theorem sum_advance (K : ℕ → A → A → ℝ) (w : A → ℝ)
    (hK : ∀ a, ∑ b, K 0 a b = 1) (hw : ∑ a, w a = 1) :
    ∑ b, advance K w b = 1 := by
  unfold advance
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hK, mul_one]
  exact hw

theorem sum_jointWeight_tail (K : ℕ → A → A → ℝ) (w : A → ℝ)
    (n : ℕ) (F : (Fin (n + 1) → A) → ℝ) :
    (∑ x : Fin (n + 2) → A, jointWeight K w (n + 1) x * F (Fin.tail x)) =
      ∑ x : Fin (n + 1) → A,
        jointWeight (fun i => K (i + 1)) (advance K w) n x * F x := by
  rw [FiniteChain.sum_cons]
  simp only [jointWeight_cons, weight, Fin.tail_cons]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [jointWeight, advance, Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [weight_eq_prod]
  simp only [Fin.cons_self_tail, Fin.tail]
  ring

theorem coordinateMean_succ (K : ℕ → A → A → ℝ) (w f : A → ℝ)
    (n : ℕ) (i : Fin (n + 1)) :
    coordinateMean K w f (n + 1) i.succ =
      coordinateMean (fun j => K (j + 1)) (advance K w) f n i := by
  exact sum_jointWeight_tail K w n (fun x => f (x i))

theorem coordinateMean_zero (K : ℕ → A → A → ℝ) (w f : A → ℝ)
    (hK : ∀ i a, ∑ b, K i a b = 1) (n : ℕ) :
    coordinateMean K w f n 0 = ∑ a, w a * f a := by
  unfold coordinateMean
  rw [FiniteChain.sum_cons]
  simp only [jointWeight_cons, Fin.cons_zero]
  apply Finset.sum_congr rfl
  intro a _
  calc
    (∑ x, w a * weight K n a x * f a) =
        w a * f a * ∑ x, weight K n a x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = _ := by rw [sum_weight K hK, mul_one]

theorem coordinateMean_affine (K : ℕ → A → A → ℝ) (w f : A → ℝ)
    (p q : ℕ → ℝ) (hw : ∑ a, w a = 1)
    (hK : ∀ i a, ∑ b, K i a b = 1)
    (hmean : ∀ i a, ∑ b, K i a b * f b = p i + q i * f a)
    (n : ℕ) (i : Fin n) :
    coordinateMean K w f n i.succ =
      p i + q i * coordinateMean K w f n i.castSucc := by
  induction n generalizing K w p q with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [coordinateMean_succ, coordinateMean_zero _ _ _ (fun i => hK (i + 1)),
        show (Fin.castSucc (0 : Fin (n + 1))) = 0 by rfl,
        coordinateMean_zero K w f hK]
      simp only [Fin.val_zero]
      unfold advance
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      calc
        (∑ a, ∑ b, w a * K 0 a b * f b) =
            ∑ a, w a * (p 0 + q 0 * f a) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [← hmean 0 a, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b _
          ring
        _ = _ := by
          simp_rw [mul_add]
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, hw, one_mul]
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a _
          ring
    · rw [coordinateMean_succ, show j.succ.castSucc = j.castSucc.succ by rfl,
        coordinateMean_succ]
      exact ih (fun k => K (k + 1)) (advance K w)
        (fun k => p (k + 1)) (fun k => q (k + 1))
        (sum_advance K w (hK 0) hw) (fun k => hK (k + 1))
        (fun k => hmean (k + 1)) j

end Problem367.InhomogeneousChain

end

end OAI
