import OAI.Probability.InvariantIsing.Cavity.ConsecutiveBlockSplit

namespace OAI

/-! Dimension transport for consecutive constrained blocks. The successor
constraint is exactly the base/cavity product, including its cube mass. -/

noncomputable section
open IsingPerceptron

namespace InvariantIsing

def spinDimensionCast {N M : ℕ} (h : N = M) : Spin N ≃ Spin M where
  toFun σ i := σ (Fin.cast h.symm i)
  invFun σ i := σ (Fin.cast h i)
  left_inv σ := by funext i; simp
  right_inv σ := by funext i; simp

lemma spin_family_dimension_cast {α : Sort*}
    (F : (N : ℕ) → Finset (Spin N) → α) {N M : ℕ}
    (h : N = M) (S : Finset (Spin N)) :
    F M (S.map (spinDimensionCast h).toEmbedding) = F N S := by
  subst M
  congr 1
  ext σ
  simp [spinDimensionCast]

lemma consecutive_spin_family_succ {α : Sort*}
    (F : (N : ℕ) → Finset (Spin N) → α) (n K : ℕ) (C : Finset (Spin n)) :
    F ((K+1)*n) (consecutiveBlockConstraint n (K+1) C) =
      F (K*n+n) (cavityProductSlice (consecutiveBlockConstraint n K C) C) := by
  rw [consecutiveBlockConstraint_succ]
  exact spin_family_dimension_cast F (Nat.succ_mul K n).symm _

lemma consecutiveBlockConstraint_card {n K : ℕ} (C : Finset (Spin n)) :
    (consecutiveBlockConstraint n K C).card = C.card^K := by
  induction K with
  | zero => simp [consecutiveBlockConstraint]
  | succ K ih =>
    rw [consecutiveBlockConstraint_succ, Finset.card_map, cavityProductSlice_card, ih, pow_succ]

lemma consecutiveBlockConstraint_log_mass {n K : ℕ} (C : Finset (Spin n)) :
    Real.log (consecutiveBlockConstraint n K C).card - (K*n : ℕ)*Real.log 2 =
      (K : ℝ)*(Real.log C.card-n*Real.log 2) := by
  rw [consecutiveBlockConstraint_card, Nat.cast_pow, Real.log_pow]
  push_cast
  ring

lemma consecutiveBlockConstraint_log_mass_succ {n K : ℕ} (C : Finset (Spin n)) :
    (Real.log (consecutiveBlockConstraint n (K+1) C).card - ((K+1)*n : ℕ)*Real.log 2) -
      (Real.log (consecutiveBlockConstraint n K C).card - (K*n : ℕ)*Real.log 2) =
      Real.log C.card-n*Real.log 2 := by
  rw [consecutiveBlockConstraint_log_mass C, consecutiveBlockConstraint_log_mass C]
  push_cast
  ring

end InvariantIsing

end

end OAI
