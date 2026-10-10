import OAI.NumberTheory.Ostmann.Construction.BinnedWordNorm
import OAI.NumberTheory.Ostmann.Construction.TopWordBinScale

namespace OAI

/-! # Uniform rates when selecting the actual initial character word bin -/
namespace Ostmann
open scoped Classical BigOperators

theorem character_word_bin_selection {P B : Type*} [Fintype P] [Fintype B] [Nonempty B]
    (m : ℕ) (L X A C δ : ℝ) (hm : 1 ≤ m) (hLm : L ≤ m)
    (hX : 0 < X) (hC : 0 ≤ C) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (E : Finset ℕ) (hE : Real.sqrt X * Real.exp (-A * m) ≤ E.card)
    (μ : Fin (m + 1) → P → ℝ) (F : ℕ → Fin (m + 1) → P → ℂ)
    (bin : (Fin (m + 1) → P) → B)
    (hcount : (Fintype.card B : ℝ) ≤ Real.exp (C * L))
    (hmean : ∀ a ∈ E, ∀ i, δ ≤ ‖∑ p, (μ i p : ℂ) * F a i p‖) :
    ∃ b : B, ∃ S : Finset ℕ, S ⊆ E ∧ S.Nonempty ∧
      Real.sqrt X * Real.exp (-(A + C) * m) ≤ S.card ∧
      ∀ a ∈ S, Real.exp (-(C - 2 * Real.log δ) * m) ≤
        ‖binnedWordAverage μ (F a) bin b‖ := by
  obtain ⟨b, S, hSE, hcard, hword⟩ := common_large_word_bin_of_norm E μ F bin δ hδ.le hmean
  have hK : (Fintype.card B : ℝ) ≤ Real.exp (C * m) :=
    hcount.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hLm hC))
  have hcard₀ : (E.card : ℝ) ≤ (Fintype.card B : ℝ) * S.card := by
    exact_mod_cast hcard
  have hcard' : (E.card : ℝ) ≤ Real.exp (C * m) * S.card :=
    hcard₀.trans (mul_le_mul_of_nonneg_right hK (Nat.cast_nonneg _))
  have hS : Real.sqrt X * Real.exp (-(A + C) * m) ≤ S.card := by
    apply (mul_le_mul_iff_right₀ (Real.exp_pos (C * m))).mp
    calc
      _ = Real.sqrt X * Real.exp (-A * m) := by
        calc
          _ = Real.sqrt X * Real.exp (C * m + -(A + C) * m) := by
            rw [Real.exp_add]; ring
          _ = _ := by congr 2; ring
      _ ≤ E.card := hE
      _ ≤ _ := by simpa only [mul_comm] using hcard'
  have hSpos : 0 < (S.card : ℝ) :=
    (mul_pos (Real.sqrt_pos.mpr hX) (Real.exp_pos _)).trans_le hS
  refine ⟨b, S, hSE, Finset.card_pos.mp (by exact_mod_cast hSpos), hS, ?_⟩
  intro a ha
  have hlog : Real.log δ ≤ 0 := Real.log_nonpos hδ.le hδ1
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hpow : Real.exp (2 * Real.log δ * m) ≤ δ ^ (m + 1) := by
    calc
      _ ≤ Real.exp ((m + 1 : ℕ) * Real.log δ) := by
        apply Real.exp_le_exp.mpr
        push_cast
        nlinarith only [hlog, hm']
      _ = _ := by rw [Real.exp_nat_mul, Real.exp_log hδ]
  have hnorm := norm_nonneg (binnedWordAverage μ (F a) bin b)
  have he := (hpow.trans (hword a ha)).trans (mul_le_mul_of_nonneg_right hK hnorm)
  apply (mul_le_mul_iff_right₀ (Real.exp_pos (C * m))).mp
  calc
    _ = Real.exp (2 * Real.log δ * m) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := by simpa only [mul_comm] using he

end Ostmann

end OAI
