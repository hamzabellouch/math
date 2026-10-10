import OAI.Probability.FreeIsing.Estimates.FiniteChain
import OAI.Probability.FreeIsing.Spins.Kernel

namespace OAI

noncomputable section

namespace Problem367

def spinPathWeight (theta : ℝ) (n : ℕ) (x : Fin (n+1) → IsingSpin) : ℝ :=
  ∏ i : Fin n, transitionKernel theta (x i.castSucc) (x i.succ)

theorem spinPathWeight_cons (theta : ℝ) (n : ℕ) (a : IsingSpin)
    (x : Fin n → IsingSpin) :
    spinPathWeight theta n (Fin.cons a x) =
      FiniteChain.weight (transitionKernel theta) n a x := by
  rw [FiniteChain.weight_eq_prod]
  simp [spinPathWeight]

theorem spinChain_expectation (theta : ℝ) (n : ℕ) (a : IsingSpin) :
    ∑ x : Fin n → IsingSpin,
      FiniteChain.weight (transitionKernel theta) n a x *
        spinSign (FiniteChain.endpoint n a x) = theta^n * spinSign a :=
  FiniteChain.expectation_eigenfunction (transitionKernel theta) spinSign theta
    (transitionKernel_spinSum theta) n a

theorem spinChain_endpoint_distribution (theta : ℝ) (n : ℕ) (a b : IsingSpin) :
    FiniteChain.expectation (transitionKernel theta) n
      (fun c => if c = b then 1 else 0) a = transitionKernel (theta^n) a b := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [FiniteChain.expectation_succ]
    simp_rw [ih]
    rw [transitionKernel_comp, pow_succ']

theorem spinPathWeight_endpoints (theta : ℝ) (n : ℕ) (a b : IsingSpin) :
    ∑ x : Fin (n+1) → IsingSpin,
      (1/2 : ℝ) * spinPathWeight theta n x *
        (if x 0 = a ∧ x (Fin.last n) = b then 1 else 0) =
      (1/2 : ℝ) * transitionKernel (theta^n) a b := by
  rw [FiniteChain.sum_cons]
  simp only [spinPathWeight_cons, Fin.cons_zero, ← FiniteChain.endpoint_eq_last]
  calc
    _ = (1/2 : ℝ) * FiniteChain.expectation (transitionKernel theta) n
        (fun c => if c = b then 1 else 0) a := by
      rw [FiniteChain.expectation, Finset.mul_sum]
      rw [Finset.sum_eq_single a]
      · apply Finset.sum_congr rfl
        intro x hx
        simp only [true_and, mul_assoc]
      · intro c hc hca
        simp [hca]
      · simp
    _ = _ := by rw [spinChain_endpoint_distribution]

theorem spinPathWeight_correlation (theta : ℝ) (n : ℕ) :
    ∑ x : Fin (n+1) → IsingSpin,
      (1/2 : ℝ) * spinPathWeight theta n x * spinSign (x 0) *
        spinSign (x (Fin.last n)) = theta^n := by
  rw [FiniteChain.sum_cons]
  simp only [spinPathWeight_cons, Fin.cons_zero,
    ← FiniteChain.endpoint_eq_last]
  have hinner (a : IsingSpin) :
      (∑ x : Fin n → IsingSpin,
        (1/2 : ℝ) * FiniteChain.weight (transitionKernel theta) n a x * spinSign a *
          spinSign (FiniteChain.endpoint n a x)) = (1/2 : ℝ) * theta^n := by
    calc
      _ = (1/2 : ℝ) * spinSign a *
          ∑ x : Fin n → IsingSpin,
            FiniteChain.weight (transitionKernel theta) n a x *
              spinSign (FiniteChain.endpoint n a x) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        ring
      _ = (1/2 : ℝ) * theta^n := by
        rw [spinChain_expectation]
        calc
          _ = (1/2 : ℝ) * theta^n * (spinSign a * spinSign a) := by ring
          _ = _ := by rw [spinSign_mul_self, mul_one]
  simp_rw [hinner]
  rw [sum_isingSpin]
  ring

theorem spinPathWeight_sum (theta : ℝ) (n : ℕ) :
    ∑ x : Fin (n+1) → IsingSpin, (1/2 : ℝ) * spinPathWeight theta n x = 1 := by
  rw [FiniteChain.sum_cons]
  simp only [spinPathWeight_cons, ← Finset.mul_sum]
  simp only [FiniteChain.sum_weight _ (transitionKernel_sum theta)]
  rw [sum_isingSpin]
  norm_num

theorem spinPathWeight_nonneg {theta : ℝ} (hlo : -1 ≤ theta) (hhi : theta ≤ 1)
    (n : ℕ) (x : Fin (n+1) → IsingSpin) : 0 ≤ spinPathWeight theta n x := by
  exact Finset.prod_nonneg fun _ _ => transitionKernel_nonneg hlo hhi _ _

end Problem367

end

end OAI
