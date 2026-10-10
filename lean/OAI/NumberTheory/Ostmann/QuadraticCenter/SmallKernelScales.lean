import OAI.NumberTheory.Ostmann.QuadraticCenter.SmallDivisorEnergy

namespace OAI

/-! # The concrete small-kernel scale inequality for all divisor moduli -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap

theorem small_kernel_scale_bound (L q s : ℕ) (R v : ℝ)
    (hs : 0 < s) (hv : 0 < v) (hqL : q ≤ L) (hsL : s ≤ L ^ 4)
    (hvL : v ≤ L) (hR : (L : ℝ) ^ 6 ≤ R) :
    (q : ℝ) ≤ Real.sqrt (R * q / ((s : ℝ) * v)) := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hqR : (q : ℝ) ≤ L := Nat.cast_le.mpr hqL
  have hsR' : (s : ℝ) ≤ (L : ℝ) ^ 4 := by exact_mod_cast hsL
  have hprod : (q : ℝ) * s * v ≤ (L : ℝ) ^ 6 := by
    calc
      _ ≤ ((L : ℝ) * L ^ 4) * L := by gcongr
      _ = _ := by ring
  apply Real.le_sqrt_of_sq_le
  apply (le_div_iff₀ (mul_pos hsR hv)).mpr
  have hh := mul_le_mul_of_nonneg_left (hprod.trans hR) (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
  nlinarith only [hh]

/-- The manuscript's range `s <= L^4`, `v <= L` and `R >= L^6`
automatically supplies the small-kernel bound for every divisor of `L`. -/
theorem eventual_small_kernel_norm_from_ranges (C₀ H ε : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (hH : 0 ≤ H) (hε : 0 < ε) (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ∀ᶠ T : ℝ in atTop, ∀ (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
      (M : ℕ) (S : Finset ℕ) (u : ℝ),
      (M : ℝ) ≤ Real.exp (C₀ * T) → (P.card : ℝ) ≤ T ^ (9999999 / 10000000 : ℝ) →
      (∀ s ∈ S, Squarefree s ∧ s ≤ M ∧ s ≤ P.toList.prod ^ 4) →
      0 ≤ u → u ≤ 4 * T ^ (1 / 1000000 : ℝ) →
      ∀ (D : ∀ p : ℕ, Finset (ZMod p))
        (a : ∀ U : Finset ℕ, ZMod U.toList.prod) (θ : Finset ℕ → ℝ)
        (R v : ℝ) (c : Finset ℕ → ℂ),
      (P.toList.prod : ℝ) ^ 6 ≤ R → 0 < v → v ≤ P.toList.prod →
      (∀ U ∈ P.powerset, ‖c U‖ ≤ (1 / 16 : ℝ) ^ U.card) →
      Real.sqrt (∑ s ∈ S, (u ^ s.primeFactors.card / (s : ℝ)) *
        ‖∑ U ∈ P.powerset, c U * primeDivisorPositive P hP D a θ Φ R v U s‖ ^ 2) ≤
        Real.exp ((1 / 10 + ε) * T ^ (9999999 / 10000000 : ℝ)) := by
  filter_upwards [eventual_small_kernel_positive_norm C₀ H ε Φ hH hε hΦ] with T hT
  intro P hP M S u hM hcard hS hu huU D a θ R v c hR hv hvL hc
  have hL : (0 : ℝ) < P.toList.prod := by exact_mod_cast prime_list_prod_pos _ (primeSet_list_prime P hP)
  have hR0 : 0 < R := lt_of_lt_of_le (pow_pos hL 6) hR
  apply hT P hP M S u hM hcard (fun s hs => ⟨(hS s hs).1, (hS s hs).2.1⟩) hu huU
    D a θ R v c hR0 hv hc
  intro s hs U hU
  exact small_kernel_scale_bound P.toList.prod U.toList.prod s R v
    (Nat.pos_of_ne_zero (hS s hs).1.ne_zero) hv (primeSet_prod_le_of_subset P U hP hU)
    (hS s hs).2.2 hvL hR

end Ostmann

end OAI
