import OAI.NumberTheory.Ostmann.Construction.SpectatorBulkScale
import OAI.NumberTheory.Ostmann.Construction.InitialHalfListWeights

namespace OAI

/-! # Exact normalization cost of the two original mixed half-lists -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def initialHalfNormalizer (b d r : ℕ) (a L g : ℝ) :
    Fin ((b + (d + r)) + 1) → ℝ :=
  Fin.cons (Real.exp (g * L))
    (Fin.append (fun _ : Fin b => (a * L)⁻¹)
      (Fin.append (fun _ : Fin d => (a * L)⁻¹) (fun _ : Fin r => Real.exp (2 * L))))

theorem initialHalfNormalizer_nonneg (b d r : ℕ) (a L g : ℝ)
    (ha : 0 ≤ a) (hL : 0 ≤ L) : ∀ i, 0 ≤ initialHalfNormalizer b d r a L g i := by
  intro i
  refine Fin.cases (Real.exp_nonneg _) (fun j => ?_) i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simpa only [initialHalfNormalizer, Fin.cons_succ, Fin.append_left] using
      inv_nonneg.mpr (mul_nonneg ha hL)
  · refine Fin.addCases (fun t => ?_) (fun t => ?_) j
    · simpa only [initialHalfNormalizer, Fin.cons_succ, Fin.append_right, Fin.append_left] using
        inv_nonneg.mpr (mul_nonneg ha hL)
    · simpa only [initialHalfNormalizer, Fin.cons_succ, Fin.append_right] using
        Real.exp_nonneg (2 * L)

theorem initialHalfNormalizer_prime_bound (P : Finset ℕ) (b d r : ℕ) (a L g : ℝ)
    (μ₀ : P → ℝ) (μb : Fin b → P → ℝ) (μd : Fin d → P → ℝ) (μc : Fin r → P → ℝ)
    (h₀ : ∀ q : P, (q : ℝ) * μ₀ q ≤ Real.exp (g * L))
    (hb : ∀ i (q : P), (q : ℝ) * μb i q ≤ (a * L)⁻¹)
    (hd : ∀ i (q : P), (q : ℝ) * μd i q ≤ (a * L)⁻¹)
    (hc : ∀ i (q : P), (q : ℝ) * μc i q ≤ Real.exp (2 * L)) :
    ∀ i (q : P), (q : ℝ) *
      (Fin.cons μ₀ (Fin.append μb (Fin.append μd μc)) :
        Fin ((b + (d + r)) + 1) → P → ℝ) i q ≤ initialHalfNormalizer b d r a L g i := by
  intro i q
  refine Fin.cases (h₀ q) (fun j => ?_) i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simpa only [initialHalfNormalizer, Fin.cons_succ, Fin.append_left] using hb j q
  · refine Fin.addCases (fun t => ?_) (fun t => ?_) j
    · simpa only [initialHalfNormalizer, Fin.cons_succ, Fin.append_right, Fin.append_left] using hd t q
    · simpa only [initialHalfNormalizer, Fin.cons_succ, Fin.append_right] using hc t q

theorem initialHalfNormalizer_prod (b d r : ℕ) (a L g : ℝ) :
    (∏ i, initialHalfNormalizer b d r a L g i) =
      Real.exp (g * L) * ((a * L)⁻¹) ^ (b + d) * (Real.exp (2 * L)) ^ r := by
  simp only [initialHalfNormalizer, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
    Fin.prod_univ_add, Fin.append_left, Fin.append_right, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, pow_add]
  ring

theorem initial_mixed_normalizer_identity (b d r : ℕ) (a L g : ℝ)
    (ha : 0 < a) (hL : 0 < L) :
    let C := initialHalfNormalizer b d r a L g
    (∏ i, Fin.append C C i) * (a * L) ^ (2 * (b + d)) =
      Real.exp ((2 * g + 4 * r) * L) := by
  intro C
  have hC : (∏ i, C i) = Real.exp (g * L) * ((a * L)⁻¹) ^ (b + d) *
      (Real.exp (2 * L)) ^ r := initialHalfNormalizer_prod b d r a L g
  have hcancel : ((a * L)⁻¹) ^ (b + d) * (a * L) ^ (b + d) = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ (mul_pos ha hL).ne', one_pow]
  have hhalf : (∏ i, C i) * (a * L) ^ (b + d) =
      Real.exp (g * L) * (Real.exp (2 * L)) ^ r := by
    rw [hC]
    calc
      _ = (Real.exp (g * L) * (Real.exp (2 * L)) ^ r) *
          (((a * L)⁻¹) ^ (b + d) * (a * L) ^ (b + d)) := by ring
      _ = _ := by rw [hcancel, mul_one]
  calc
    _ = ((∏ i, C i) * (a * L) ^ (b + d)) ^ 2 := by
      rw [Fin.prod_univ_add]
      simp only [Fin.append_left, Fin.append_right]
      rw [show 2 * (b + d) = (b + d) * 2 by omega, pow_mul]
      ring
    _ = (Real.exp (g * L) * (Real.exp (2 * L)) ^ r) ^ 2 := by rw [hhalf]
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_nat_mul]
      congr 1
      push_cast
      ring

theorem initial_mixed_normalizer_bound (b d r : ℕ) (a L g : ℝ)
    (ha : 0 < a) (hL : 0 < L) (hcell : (2 * g + 4 * r) * L ≤ 4 * (b + d : ℕ)) :
    let C := initialHalfNormalizer b d r a L g
    (∏ i, Fin.append C C i) * L ^ (2 * (b + d)) ≤
      Real.exp ((4 - 2 * Real.log a) * (b + d : ℕ)) := by
  intro C
  have hid := initial_mixed_normalizer_identity b d r a L g ha hL
  have hpow : a ^ (2 * (b + d)) = Real.exp (((2 * (b + d) : ℕ) : ℝ) * Real.log a) := by
    rw [Real.exp_nat_mul, Real.exp_log ha]
  apply (mul_le_mul_iff_left₀ (pow_pos ha (2 * (b + d)))).mp
  calc
    _ = (∏ i, Fin.append C C i) * (a * L) ^ (2 * (b + d)) := by rw [mul_pow]; ring
    _ = Real.exp ((2 * g + 4 * r) * L) := hid
    _ ≤ Real.exp (4 * (b + d : ℕ)) := Real.exp_le_exp.mpr hcell
    _ = Real.exp ((4 - 2 * Real.log a) * (b + d : ℕ)) * a ^ (2 * (b + d)) := by
      rw [hpow, ← Real.exp_add]
      congr 1
      push_cast
      ring

theorem initial_cell_normalizer_budget (k : ℕ) (hk : 2 ≤ k) (L g : ℝ)
    (hL : 0 ≤ L) (hg : g ≤ 1) (hscale : 4 ≤ (k : ℝ) ^ 4 * L) :
    (2 * g + 4 * (3 + 2 * k : ℕ)) * L ≤ 4 * (spectatorBulkCount k L : ℝ) := by
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk3 : (8 : ℝ) ≤ (k : ℝ) ^ 3 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hk2 3
    norm_num at hh
    exact hh
  have hk4 : 8 * (k : ℝ) ≤ (k : ℝ) ^ 4 := by
    nlinarith [mul_le_mul_of_nonneg_right hk3 (show 0 ≤ (k : ℝ) by positivity)]
  have hcoef : 2 * g + 4 * (3 + 2 * k : ℕ) ≤ 2 * (k : ℝ) ^ 4 := by
    push_cast
    nlinarith
  have hprod := mul_le_mul_of_nonneg_right hcoef hL
  have hm := spectatorBulkCount_half k L hscale
  linarith

end Ostmann

end OAI
