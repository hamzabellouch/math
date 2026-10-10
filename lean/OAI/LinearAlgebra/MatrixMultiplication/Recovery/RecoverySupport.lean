import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OAI

/-! Finite orbit symmetries, masks and exact recovery operations. -/

noncomputable section

namespace MatrixMultiplication.RecoverySupport

variable {K X Y Z : Type*} [Zero K] [Fintype X] [Fintype Y] [Fintype Z]

def support (Q : X → Y → Z → K) : Finset (X × Y × Z) := by
  classical
  exact Finset.univ.filter fun p => Q p.1 p.2.1 p.2.2 ≠ 0

theorem support_card_le (Q : X → Y → Z → K) :
    (support Q).card ≤ Fintype.card X * Fintype.card Y * Fintype.card Z := by
  classical
  have h := Finset.card_filter_le (s := (Finset.univ : Finset (X × Y × Z)))
    (p := fun p => Q p.1 p.2.1 p.2.2 ≠ 0)
  simpa only [support, Finset.card_univ, Fintype.card_prod, Nat.mul_assoc] using h

theorem support_card_le_exp (Q : X → Y → Z → K) {bX bY bZ : ℝ} (N : ℕ)
    (hX : (Fintype.card X : ℝ) ≤ Real.exp (bX * N))
    (hY : (Fintype.card Y : ℝ) ≤ Real.exp (bY * N))
    (hZ : (Fintype.card Z : ℝ) ≤ Real.exp (bZ * N)) :
    ((support Q).card : ℝ) ≤ Real.exp ((bX + bY + bZ) * N) := by
  have hcard : ((support Q).card : ℝ) ≤
      (Fintype.card X : ℝ) * Fintype.card Y * Fintype.card Z := by
    exact_mod_cast support_card_le Q
  calc
    ((support Q).card : ℝ) ≤
        (Fintype.card X : ℝ) * Fintype.card Y * Fintype.card Z := hcard
    _ ≤ (Real.exp (bX * N) * Real.exp (bY * N)) * Real.exp (bZ * N) :=
      mul_le_mul (mul_le_mul hX hY (Nat.cast_nonneg _) (Real.exp_pos _).le)
        hZ (Nat.cast_nonneg _) (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    _ = Real.exp ((bX + bY + bZ) * N) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

theorem word_card_eq_exp {d : ℕ} (hd : 0 < d) (a N : ℕ) :
    (Fintype.card (Fin (a * N) → Fin d) : ℝ) =
      Real.exp (((a : ℝ) * Real.log (d : ℝ)) * N) := by
  have hdr : 0 < (d : ℝ) := by exact_mod_cast hd
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  calc
    (d : ℝ) ^ (a * N) = Real.exp (((a * N : ℕ) : ℝ) * Real.log (d : ℝ)) := by
      rw [Real.exp_nat_mul, Real.exp_log hdr]
    _ = Real.exp (((a : ℝ) * Real.log (d : ℝ)) * N) := by
      simp only [Nat.cast_mul]
      congr 1
      ring

theorem card_le_exp_of_word_embedding {d : ℕ} (hd : 0 < d) (a N : ℕ)
    (e : X ↪ (Fin (a * N) → Fin d)) :
    (Fintype.card X : ℝ) ≤ Real.exp (((a : ℝ) * Real.log (d : ℝ)) * N) := by
  rw [← word_card_eq_exp hd a N]
  exact_mod_cast Fintype.card_le_of_injective e e.injective

theorem support_card_le_exp_of_word_embeddings (Q : X → Y → Z → K)
    {d : ℕ} (hd : 0 < d) (a N : ℕ)
    (ex : X ↪ (Fin (a * N) → Fin d))
    (ey : Y ↪ (Fin (a * N) → Fin d))
    (ez : Z ↪ (Fin (a * N) → Fin d)) :
    ((support Q).card : ℝ) ≤ Real.exp ((3 * (a : ℝ) * Real.log (d : ℝ)) * N) := by
  have h := support_card_le_exp Q N
    (card_le_exp_of_word_embedding hd a N ex)
    (card_le_exp_of_word_embedding hd a N ey)
    (card_le_exp_of_word_embedding hd a N ez)
  convert h using 1
  congr 1
  ring

def cw5SupportRate (a : ℕ) : ℝ := 3 * (a : ℝ) * Real.log 7 + 1

theorem cw5SupportRate_pos (a : ℕ) : 0 < cw5SupportRate a := by
  have hlog : 0 ≤ Real.log 7 := Real.log_nonneg (by norm_num)
  have h := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) (Nat.cast_nonneg a)) hlog
  unfold cw5SupportRate
  linarith

theorem cw5_support_card_le_exp (Q : X → Y → Z → K) (a N : ℕ)
    (ex : X ↪ (Fin (a * N) → Fin 7))
    (ey : Y ↪ (Fin (a * N) → Fin 7))
    (ez : Z ↪ (Fin (a * N) → Fin 7)) :
    ((support Q).card : ℝ) ≤ Real.exp (cw5SupportRate a * N) := by
  apply (support_card_le_exp_of_word_embeddings Q (by norm_num) a N ex ey ez).trans
  apply Real.exp_le_exp.mpr
  unfold cw5SupportRate
  simp only [Nat.cast_ofNat]
  exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (Nat.cast_nonneg N)

end MatrixMultiplication.RecoverySupport

end

end OAI
