import OAI.LinearAlgebra.MatrixMultiplication.Recovery.RecoverySupport

namespace OAI

/-! Finite orbit symmetries, masks and exact recovery operations. -/

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.HistorySupport

variable {H : Type*}

abbrev HistoryWords (P : H → Type*) (l r : H → ℕ) (d : ℕ) :=
  ∀ h, P h → ((Fin (l h) → Fin d) × (Fin (r h) → Fin d))

def totalLength [Fintype H] (P : H → Type*) [∀ h, Fintype (P h)]
    (l r : H → ℕ) : ℕ :=
  ∑ h, Fintype.card (P h) * (l h + r h)

variable [Fintype H] [DecidableEq H]
variable (P : H → Type*) [∀ h, Fintype (P h)] [∀ h, DecidableEq (P h)]
variable (l r : H → ℕ)

theorem card_historyWords (d : ℕ) :
    Fintype.card (HistoryWords P l r d) = d ^ totalLength P l r := by
  change Fintype.card (∀ h, P h → ((Fin (l h) → Fin d) × (Fin (r h) → Fin d))) = _
  rw [Fintype.card_pi]
  simp only [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin, ← pow_add, ← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  unfold totalLength
  apply Finset.sum_congr rfl
  intro h _
  exact Nat.mul_comm _ _

theorem card_historyWords_le_pow {d : ℕ} (hd : 0 < d) (a N : ℕ)
    (hlen : totalLength P l r ≤ a * N) :
    Fintype.card (HistoryWords P l r d) ≤ d ^ (a * N) := by
  rw [card_historyWords]
  exact Nat.pow_le_pow_right hd hlen

theorem card_historyWords_le_exp {d : ℕ} (hd : 0 < d) (a N : ℕ)
    (hlen : totalLength P l r ≤ a * N) :
    (Fintype.card (HistoryWords P l r d) : ℝ) ≤
      Real.exp (((a : ℝ) * Real.log (d : ℝ)) * N) := by
  have hpow : ((d ^ (a * N) : ℕ) : ℝ) =
      Real.exp (((a : ℝ) * Real.log (d : ℝ)) * N) := by
    simpa only [Fintype.card_fun, Fintype.card_fin] using
      RecoverySupport.word_card_eq_exp hd a N
  rw [← hpow]
  exact_mod_cast card_historyWords_le_pow P l r hd a N hlen

theorem support_card_le_exp {K : Type*} [Zero K] {d : ℕ} (hd : 0 < d)
    (Q : HistoryWords P l r d → HistoryWords P l r d → HistoryWords P l r d → K)
    (a N : ℕ) (hlen : totalLength P l r ≤ a * N) :
    ((RecoverySupport.support Q).card : ℝ) ≤
      Real.exp ((3 * (a : ℝ) * Real.log (d : ℝ)) * N) := by
  have hdim := card_historyWords_le_exp P l r hd a N hlen
  have h := RecoverySupport.support_card_le_exp Q N hdim hdim hdim
  convert h using 1
  congr 1
  ring

theorem cw5_support_card_le_exp {K : Type*} [Zero K]
    (Q : HistoryWords P l r 7 → HistoryWords P l r 7 → HistoryWords P l r 7 → K)
    (a N : ℕ) (hlen : totalLength P l r ≤ a * N) :
    ((RecoverySupport.support Q).card : ℝ) ≤
      Real.exp (RecoverySupport.cw5SupportRate a * N) := by
  apply (support_card_le_exp P l r (by norm_num) Q a N hlen).trans
  apply Real.exp_le_exp.mpr
  unfold RecoverySupport.cw5SupportRate
  simp only [Nat.cast_ofNat]
  exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (Nat.cast_nonneg N)

end MatrixMultiplication.HistorySupport

end

end OAI
