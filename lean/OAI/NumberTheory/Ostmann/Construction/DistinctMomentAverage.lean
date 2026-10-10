import Mathlib.Data.Fintype.CardEmbedding
import OAI.NumberTheory.Ostmann.Construction.WeightedRepeatRemoval

namespace OAI

/-! # Passing the physical distinct moment to a uniform finite average -/

namespace Ostmann

open scoped BigOperators Classical

theorem weighted_distinct_average_le {ι A : Type*} [Fintype A] [DecidableEq A]
    (w : ι → ℝ) (y : ι → A → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hy : ∀ i a, |y i a| ≤ 1) (hws : Summable w)
    (k : ℕ) (F : (Fin k ↪ A) → ℝ) (C : ℝ)
    (hF : ∀ e, 0 ≤ F e) (hC : 0 ≤ C) (hkA : k ≤ Fintype.card A)
    (hb : ∀ e, |∑' i, w i * ∏ j, y i (e j)| ≤ C * F e) :
    (∑' i, w i * ternaryDistinctMean (y i) k) ≤
      C * ((Fintype.card (Fin k ↪ A) : ℝ)⁻¹ * ∑ e, F e) := by
  have hs (e : Fin k ↪ A) : Summable (fun i => w i * ∏ j, y i (e j)) := by
    apply Summable.of_norm_bounded hws
    intro i
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw i), Finset.abs_prod]
    have hp : (∏ j : Fin k, |y i (e j)|) ≤ 1 := by
      exact (Finset.prod_le_prod₀ (fun j _ => abs_nonneg _) (fun j _ => hy i (e j))).trans_eq
        (Finset.prod_const_one)
    exact mul_le_of_le_one_right (hw i) hp
  have he : (∑' i, w i * ternaryDistinctMean (y i) k) =
      (∑ e : Fin k ↪ A, ∑' i, w i * ∏ j, y i (e j)) / (Fintype.card A : ℝ) ^ k := by
    simp only [ternaryDistinctMean, ← mul_div_assoc, Finset.mul_sum]
    rw [tsum_div_const, Summable.tsum_finsetSum (fun e _ => hs e)]
  have hsum : (∑ e : Fin k ↪ A, ∑' i, w i * ∏ j, y i (e j)) ≤ C * ∑ e, F e := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun e _ => (le_abs_self _).trans (hb e))
  have hn : (Fintype.card (Fin k ↪ A) : ℝ) ≤ (Fintype.card A : ℝ) ^ k := by
    exact_mod_cast (show Fintype.card (Fin k ↪ A) ≤ Fintype.card A ^ k by
      rw [Fintype.card_embedding_eq, Fintype.card_fin]
      exact Nat.descFactorial_le_pow _ _)
  have hnpos : (0 : ℝ) < Fintype.card (Fin k ↪ A) := by
    exact_mod_cast (show 0 < Fintype.card (Fin k ↪ A) by
      rw [Fintype.card_embedding_eq, Fintype.card_fin]
      exact Nat.descFactorial_pos.mpr hkA)
  rw [he]
  calc
    _ ≤ (C * ∑ e, F e) / (Fintype.card A : ℝ) ^ k :=
      div_le_div_of_nonneg_right hsum (by positivity)
    _ ≤ (C * ∑ e, F e) / Fintype.card (Fin k ↪ A) :=
      div_le_div_of_nonneg_left (mul_nonneg hC (Finset.sum_nonneg (fun e _ => hF e))) hnpos hn
    _ = _ := by ring

/-- The amplified lower bound forces the uniform first moment needed by the
finite witness-probability argument. -/
theorem amplified_distinct_first_mean {ι A : Type*} [Fintype A] [DecidableEq A]
    (w : ι → ℝ) (y : ι → A → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hy : ∀ i a, |y i a| ≤ 1) (hws : Summable w)
    (k : ℕ) (F : (Fin k ↪ A) → ℝ) (X K : ℝ) (hX : 0 < X) (hK : 3000 ≤ K)
    (hF : ∀ e, 0 ≤ F e) (hkA : k ≤ Fintype.card A)
    (hb : ∀ e, |∑' i, w i * ∏ j, y i (e j)| ≤ 2 * Real.sqrt X * F e)
    (hlower : Real.sqrt X * Real.exp ((2 / 125 : ℝ) * K) / 2 ≤
      ∑' i, w i * ternaryDistinctMean (y i) k) :
    Real.exp ((3 / 200 : ℝ) * K) ≤
      (Fintype.card (Fin k ↪ A) : ℝ)⁻¹ * ∑ e, F e := by
  have hh := hlower.trans (weighted_distinct_average_le w y hw hy hws k F
    (2 * Real.sqrt X) hF (by positivity) hkA hb)
  have hroot := Real.sqrt_pos.mpr hX
  have hfour : Real.exp ((2 / 125 : ℝ) * K) / 4 ≤
      (Fintype.card (Fin k ↪ A) : ℝ)⁻¹ * ∑ e, F e := by nlinarith
  apply le_trans _ hfour
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr
  have hexp : (4 : ℝ) ≤ Real.exp (K / 1000) := by
    have h := Real.add_one_le_exp (K / 1000)
    linarith
  calc
    _ ≤ Real.exp ((3 / 200 : ℝ) * K) * Real.exp (K / 1000) := by gcongr
    _ = Real.exp ((2 / 125 : ℝ) * K) := by rw [← Real.exp_add]; congr 1; ring

end Ostmann

end OAI
