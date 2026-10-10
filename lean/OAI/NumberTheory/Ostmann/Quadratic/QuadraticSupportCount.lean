import Mathlib.Algebra.Order.Floor.Ring
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticCorrelationNormalization

namespace OAI

/-! # The support-size and scaling bounds for the expanded quadratic sums -/

namespace Ostmann

open scoped BigOperators

theorem quadratic_support_count_le (W : Finset ℕ) (Q : ℝ)
    (hW : ∀ w ∈ W, 0 < w ∧ (w : ℝ) ^ 2 ≤ Q) : (W.card : ℝ) ≤ Real.sqrt Q := by
  have hsub : W ⊆ Finset.Ioc 0 ⌊Real.sqrt Q⌋₊ := by
    intro w hw
    obtain ⟨hw0, hwQ⟩ := hW w hw
    exact Finset.mem_Ioc.mpr ⟨hw0, Nat.le_floor (Real.le_sqrt_of_sq_le hwQ)⟩
  have hc : W.card ≤ ⌊Real.sqrt Q⌋₊ := by
    simpa using Finset.card_le_card hsub
  exact (Nat.cast_le.mpr hc).trans (Nat.floor_le (Real.sqrt_nonneg Q))

theorem quadratic_support_pair_count (W V : Finset ℕ) (R d e v N C : ℝ)
    (hR : 0 < R) (hd : 0 < d) (hv : 0 < v) (hN : 0 < N) (hC : 0 ≤ C)
    (hW : ∀ w ∈ W, 0 < w ∧ (w : ℝ) ^ 2 ≤ C * R * d / (N * v))
    (hV : ∀ w ∈ V, 0 < w ∧ (w : ℝ) ^ 2 ≤ C * R * e / (N * v)) :
    (W.card : ℝ) * V.card ≤ C * R * Real.sqrt (d * e) / (N * v) := by
  have hK : 0 ≤ C * R / (N * v) := by positivity
  calc
    _ ≤ Real.sqrt (C * R * d / (N * v)) * Real.sqrt (C * R * e / (N * v)) :=
      mul_le_mul (quadratic_support_count_le W _ hW) (quadratic_support_count_le V _ hV)
        (by positivity) (Real.sqrt_nonneg _)
    _ = Real.sqrt (((C * R / (N * v)) ^ 2) * (d * e)) := by
      rw [← Real.sqrt_mul (show 0 ≤ C * R * d / (N * v) by positivity)]
      congr 1
      ring
    _ = _ := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hK]
      ring

theorem quadratic_support_scale (R d v N C : ℝ) (w : ℕ)
    (hR : 0 < R) (hd : 0 < d) (hv : 0 < v) (hN : 0 < N)
    (hw : 0 < w) (hW : (w : ℝ) ^ 2 ≤ C * R * d / (N * v)) :
    0 < R * d / (v * (w : ℝ) ^ 2) ∧ N ≤ C * (R * d / (v * (w : ℝ) ^ 2)) := by
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  constructor
  · positivity
  · have hh := (le_div_iff₀ (mul_pos hN hv)).mp hW
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (show 0 < v * (w : ℝ) ^ 2 by positivity)).mpr
    nlinarith

end Ostmann

end OAI
