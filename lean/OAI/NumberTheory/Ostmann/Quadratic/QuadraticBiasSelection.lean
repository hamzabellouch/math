import OAI.NumberTheory.Ostmann.Preliminaries.MertensPrimeBands
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticResidueTests

namespace OAI

/-! # Extracting a fixed quadratic bias from a large weighted mean -/

namespace Ostmann

open Filter
open scoped BigOperators Classical

theorem residueTestMean_abs_le_one (S : Finset ℕ) (f : ℕ → ℝ)
    (hf : ∀ r ∈ S, |f r| ≤ 1) : |residueTestMean S f| ≤ 1 := by
  by_cases hs : S.Nonempty
  · have hc : (0 : ℝ) < S.card := by exact_mod_cast hs.card_pos
    rw [residueTestMean, abs_div, abs_of_pos hc]
    apply (div_le_one hc).mpr
    calc
      |∑ r ∈ S, f r| ≤ ∑ r ∈ S, |f r| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _r ∈ S, (1 : ℝ) := Finset.sum_le_sum hf
      _ = _ := by simp
  · simp [residueTestMean, Finset.not_nonempty_iff_eq_empty.mp hs]

theorem weighted_bias_threshold (P : Finset ℕ) (w b : ℕ → ℝ) (δ : ℝ)
    (hδ : 0 ≤ δ) (hw : ∀ p ∈ P, 0 ≤ w p) (hb : ∀ p ∈ P, b p ≤ 1) :
    (∑ p ∈ P, w p * b p) - δ * (∑ p ∈ P, w p) ≤
      ∑ p ∈ P.filter (fun p => δ ≤ b p), w p := by
  have hp (p : ℕ) (hp : p ∈ P) :
      w p * b p ≤ δ * w p + if δ ≤ b p then w p else 0 := by
    split_ifs with h
    · nlinarith [mul_le_mul_of_nonneg_left (hb p hp) (hw p hp), mul_nonneg hδ (hw p hp)]
    · have hh := mul_le_mul_of_nonneg_left (le_of_not_ge h) (hw p hp)
      linarith
  have hh := Finset.sum_le_sum hp
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_filter] at hh
  linarith only [hh]

noncomputable def biasedPrimeBand (A : Set ℕ) (N : ℕ) (T δ : ℝ) (t : ℕ → ℤ) : Finset ℕ :=
  (logPrimeBand T).filter fun p => δ ≤ |residueTestMean (tailSupport A N p) (quadraticResidueTest p (t p))|

theorem biasedPrimeBand_weight (A : Set ℕ) (N : ℕ) (T δ C : ℝ) (t : ℕ → ℤ)
    (hT : 1 ≤ T) (hC : Real.log 2 + 2 * C ≤ T) (hM : MertensEstimate C)
    (hδ : 0 ≤ δ)
    (hbias : δ * T ≤ ∑ p ∈ logPrimeBand T, (Real.log (p : ℝ) / p) *
      |residueTestMean (tailSupport A N p) (quadraticResidueTest p (t p))|) :
    δ * T / 2 ≤ ∑ p ∈ biasedPrimeBand A N T (δ / 4) t, Real.log (p : ℝ) / p := by
  have htotal : (∑ p ∈ logPrimeBand T, Real.log (p : ℝ) / p) ≤ 2 * T := by
    linarith [(logPrimeBand_weight_bounds T C hT hM).2]
  have hw (p : ℕ) (hp : p ∈ logPrimeBand T) : 0 ≤ Real.log (p : ℝ) / p :=
    div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg _)
  have hh := weighted_bias_threshold (logPrimeBand T) (fun p => Real.log (p : ℝ) / p)
    (fun p => |residueTestMean (tailSupport A N p) (quadraticResidueTest p (t p))|)
    (δ / 4) (by positivity) hw
    (fun p _ => residueTestMean_abs_le_one _ _ (fun r _ => quadraticResidueTest_abs_le p (t p) r))
  change _ ≤ ∑ p ∈ biasedPrimeBand A N T (δ / 4) t, Real.log (p : ℝ) / p at hh
  nlinarith only [hh, hbias, mul_nonneg hδ (sub_nonneg.mpr htotal)]

end Ostmann

end OAI
