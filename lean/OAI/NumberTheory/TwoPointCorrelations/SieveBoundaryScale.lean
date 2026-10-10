import OAI.NumberTheory.TwoPointCorrelations.SieveScale

namespace OAI

/-! Explicit accounting for the finite CRT boundary term. -/

namespace TwoPointCorrelations

open Filter

lemma sieve_boundary_numerator (X T C C₀ B : ℝ) (R : ℕ)
    (hX : 1 ≤ X) (hT : 1 ≤ T) (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀)
    (hB : 0 ≤ B) (hBexp : B ≤ Real.exp (3 * X)) (hR : (R : ℝ) ≤ C * T) :
    C₀ * (R + 1 : ℕ) * B ^ R ≤ Real.exp ((C₀ + 4 * C) * X * T) := by
  have hXT : 1 ≤ X * T := by nlinarith
  have hpow : B ^ R ≤ Real.exp ((R : ℝ) * (3 * X)) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ hB hBexp R
  have hRexp : (R + 1 : ℕ) ≤ Real.exp (R : ℝ) := by
    exact_mod_cast Real.add_one_le_exp (R : ℝ)
  have hCexp : C₀ ≤ Real.exp C₀ := by linarith [Real.add_one_le_exp C₀]
  calc
    _ ≤ Real.exp C₀ * Real.exp (R : ℝ) * Real.exp ((R : ℝ) * (3 * X)) := by
      gcongr
    _ = Real.exp (C₀ + (R : ℝ) + (R : ℝ) * (3 * X)) := by
      rw [← Real.exp_add, ← Real.exp_add]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have h₀ : C₀ ≤ C₀ * (X * T) := by nlinarith
      have h₁ : (R : ℝ) ≤ C * X * T := by
        have hh := mul_le_mul_of_nonneg_left hX (mul_nonneg hC (by linarith : 0 ≤ T))
        nlinarith
      have h₂ := mul_le_mul_of_nonneg_right hR (show 0 ≤ 3 * X by linarith)
      nlinarith

lemma sieve_base_le_exp (X Y n : ℝ) (hX : 1 ≤ X)
    (hY : 0 ≤ Y) (_hn : 0 ≤ n) (hnY : n ≤ Y) (hYexp : Y ≤ Real.exp X) :
    n * Y + 1 ≤ Real.exp (3 * X) := by
  have he : 2 ≤ Real.exp X := by linarith [Real.add_one_le_exp X]
  have he₂ : 1 ≤ Real.exp (2 * X) := Real.one_le_exp (by linarith)
  calc
    _ ≤ Real.exp X * Real.exp X + 1 := by
      gcongr
      exact hnY.trans hYexp
    _ = Real.exp (2 * X) + 1 := by rw [← Real.exp_add]; congr 2; ring
    _ ≤ Real.exp (2 * X) * Real.exp X := by nlinarith
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- Uniformly in the modulus cutoff, number of moduli and logarithmic
truncation order, the literal finite boundary term is `O(L^-100)`. -/
theorem eventually_sieve_boundary_cost (C C₀ : ℝ) (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀) :
    ∀ᶠ L : ℝ in atTop, ∀ (Y n : ℝ) (N R : ℕ),
      0 ≤ Y → 0 ≤ n → n ≤ Y → Y ≤ Real.exp (L ^ (99 / 100 : ℝ)) →
      (R : ℝ) ≤ C * Real.log L →
      (1 / 2 : ℝ) * Real.exp (L ^ (199 / 200 : ℝ)) ≤ N →
      C₀ / (N : ℝ) * (R + 1 : ℕ) * (n * Y + 1) ^ R ≤ L ^ (-100 : ℝ) := by
  have hK : 0 ≤ C₀ + 4 * C + 1 := by positivity
  filter_upwards [eventually_ge_atTop (Real.exp 1),
    eventually_sieve_boundary_exponent (C₀ + 4 * C + 1) hK] with L hL hsmall
  intro Y n N R hY hn hnY hYexp hR hN
  have hL₁ : 1 ≤ L := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hL
  have hLp : 0 < L := zero_lt_one.trans_le hL₁
  have hlog : 1 ≤ Real.log L := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hL
  have hX : 1 ≤ L ^ (99 / 100 : ℝ) := Real.one_le_rpow hL₁ (by norm_num)
  have hXT : 1 ≤ L ^ (99 / 100 : ℝ) * Real.log L := by nlinarith
  have hnum := sieve_boundary_numerator (L ^ (99 / 100 : ℝ)) (Real.log L) C C₀
    (n * Y + 1) R hX hlog hC hC₀ (by positivity)
    (sieve_base_le_exp _ _ _ hX hY hn hnY hYexp) hR
  have hNp : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hN
  have hdiv : (1 / (N : ℝ)) ≤ 2 * Real.exp (-(L ^ (199 / 200 : ℝ))) := by
    apply (div_le_iff₀ hNp).mpr
    have hh := mul_le_mul_of_nonneg_left hN
      (show 0 ≤ 2 * Real.exp (-(L ^ (199 / 200 : ℝ))) by positivity)
    have hc : (2 * Real.exp (-(L ^ (199 / 200 : ℝ)))) *
        ((1 / 2 : ℝ) * Real.exp (L ^ (199 / 200 : ℝ))) = 1 := by
      calc
        _ = Real.exp (-(L ^ (199 / 200 : ℝ))) *
            Real.exp (L ^ (199 / 200 : ℝ)) := by ring
        _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    rw [hc] at hh
    nlinarith only [hh]
  calc
    _ = (C₀ * (R + 1 : ℕ) * (n * Y + 1) ^ R) * (1 / (N : ℝ)) := by ring
    _ ≤ Real.exp ((C₀ + 4 * C) * L ^ (99 / 100 : ℝ) * Real.log L) *
        (2 * Real.exp (-(L ^ (199 / 200 : ℝ)))) := by gcongr
    _ ≤ Real.exp (L ^ (99 / 100 : ℝ) * Real.log L) *
        Real.exp ((C₀ + 4 * C) * L ^ (99 / 100 : ℝ) * Real.log L) *
          Real.exp (-(L ^ (199 / 200 : ℝ))) := by
      have he : 2 ≤ Real.exp (L ^ (99 / 100 : ℝ) * Real.log L) := by
        linarith [Real.add_one_le_exp (L ^ (99 / 100 : ℝ) * Real.log L)]
      calc
        _ = 2 * (Real.exp ((C₀ + 4 * C) * L ^ (99 / 100 : ℝ) * Real.log L) *
            Real.exp (-(L ^ (199 / 200 : ℝ)))) := by ring
        _ ≤ Real.exp (L ^ (99 / 100 : ℝ) * Real.log L) *
            (Real.exp ((C₀ + 4 * C) * L ^ (99 / 100 : ℝ) * Real.log L) *
              Real.exp (-(L ^ (199 / 200 : ℝ)))) :=
          mul_le_mul_of_nonneg_right he (by positivity)
        _ = _ := by ring
    _ = Real.exp ((C₀ + 4 * C + 1) * L ^ (99 / 100 : ℝ) * Real.log L -
        L ^ (199 / 200 : ℝ)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := hsmall

end TwoPointCorrelations

end OAI
