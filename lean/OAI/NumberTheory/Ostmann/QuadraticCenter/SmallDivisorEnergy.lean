import OAI.NumberTheory.Ostmann.QuadraticCenter.SmallPositiveQuadratic
import OAI.NumberTheory.Ostmann.QuadraticCenter.PositiveDivisorEnergy
import OAI.NumberTheory.Ostmann.Characters.SquarefreeCoefficientBudget

namespace OAI

/-! # The small-kernel divisor sum and its weighted square norm -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap

theorem sum_powerset_power_card (P : Finset ℕ) (x : ℝ) :
    (∑ U ∈ P.powerset, x ^ U.card) = (1 + x) ^ P.card := by
  simpa only [Finset.prod_const] using (Finset.prod_one_add (f := fun _ : ℕ => x) P).symm

theorem small_divisor_combination_bound (P : Finset ℕ) (c G : Finset ℕ → ℂ)
    (B : ℝ) (_hB : 0 ≤ B)
    (hc : ∀ U ∈ P.powerset, ‖c U‖ ≤ (1 / 16 : ℝ) ^ U.card)
    (hG : ∀ U ∈ P.powerset, ‖G U‖ ≤ B * (Real.sqrt 2) ^ U.card) :
    ‖∑ U ∈ P.powerset, c U * G U‖ ≤ B * (1 + Real.sqrt 2 / 16) ^ P.card := by
  calc
    _ ≤ ∑ U ∈ P.powerset, ‖c U * G U‖ := norm_sum_le _ _
    _ ≤ ∑ U ∈ P.powerset, B * (Real.sqrt 2 / 16) ^ U.card := by
      apply Finset.sum_le_sum
      intro U hU
      rw [norm_mul]
      have hh := mul_le_mul (hc U hU) (hG U hU) (norm_nonneg _) (by positivity)
      convert hh using 1
      simp only [div_pow, one_pow]
      ring
    _ = B * (1 + Real.sqrt 2 / 16) ^ P.card := by
      rw [← Finset.mul_sum, sum_powerset_power_card]

theorem sqrt_weighted_energy_le_uniform {ι : Type*} (S : Finset ι) (μ : ι → ℝ)
    (f : ι → ℂ) (B : ℝ) (hB : 0 ≤ B) (hμ : ∀ s ∈ S, 0 ≤ μ s)
    (hf : ∀ s ∈ S, ‖f s‖ ≤ B) :
    Real.sqrt (∑ s ∈ S, μ s * ‖f s‖ ^ 2) ≤ B * Real.sqrt (∑ s ∈ S, μ s) := by
  have hh : (∑ s ∈ S, μ s * ‖f s‖ ^ 2) ≤ B ^ 2 * ∑ s ∈ S, μ s := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s hs
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hf s hs) 2) (hμ s hs)).trans_eq (by ring)
  apply (Real.sqrt_le_sqrt hh).trans_eq
  rw [Real.sqrt_mul (sq_nonneg B), Real.sqrt_sq hB]

theorem primeDivisorPositive_small_bound (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (a : ∀ U : Finset ℕ, ZMod U.toList.prod)
    (θ : Finset ℕ → ℝ) (Φ : 𝓢(ℝ, ℂ)) (R v H : ℝ) (s : ℕ)
    (hR : 0 < R) (hv : 0 < v) (hH : 0 ≤ H) (hs : 0 < s)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0)
    (hscale : ∀ U ⊆ P, (U.toList.prod : ℝ) ≤ Real.sqrt (R * U.toList.prod / ((s : ℝ) * v)))
    (U : Finset ℕ) (hU : U ⊆ P) :
    ‖primeDivisorPositive P hP D a θ Φ R v U s‖ ≤
      (SchwartzMap.seminorm ℝ 0 0 Φ * (Real.sqrt H + 1) * Real.sqrt 2) * (Real.sqrt 2) ^ U.card := by
  let : NeZero U.toList.prod := ⟨(prime_list_prod_pos _
    (primeSet_list_prime U (fun p hp => hP p (hU hp)))).ne'⟩
  simp only [primeDivisorPositive, dite_eq_left hU]
  exact primeSet_positive_small_bound U (fun p hp => hP p (hU hp)) D (a U) (θ U) Φ R v H s
    hR hv hH hs hΦ (hscale U hU)

theorem eventual_small_kernel_positive_norm (C₀ H ε : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (hH : 0 ≤ H) (hε : 0 < ε) (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ∀ᶠ T : ℝ in atTop, ∀ (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
      (M : ℕ) (S : Finset ℕ) (u : ℝ),
      (M : ℝ) ≤ Real.exp (C₀ * T) → (P.card : ℝ) ≤ T ^ (9999999 / 10000000 : ℝ) →
      (∀ s ∈ S, Squarefree s ∧ s ≤ M) → 0 ≤ u → u ≤ 4 * T ^ (1 / 1000000 : ℝ) →
      ∀ (D : ∀ p : ℕ, Finset (ZMod p))
        (a : ∀ U : Finset ℕ, ZMod U.toList.prod) (θ : Finset ℕ → ℝ)
        (R v : ℝ) (c : Finset ℕ → ℂ),
      0 < R → 0 < v → (∀ U ∈ P.powerset, ‖c U‖ ≤ (1 / 16 : ℝ) ^ U.card) →
      (∀ s ∈ S, ∀ U ⊆ P, (U.toList.prod : ℝ) ≤ Real.sqrt (R * U.toList.prod / ((s : ℝ) * v))) →
      Real.sqrt (∑ s ∈ S, (u ^ s.primeFactors.card / (s : ℝ)) *
        ‖∑ U ∈ P.powerset, c U * primeDivisorPositive P hP D a θ Φ R v U s‖ ^ 2) ≤
        Real.exp ((1 / 10 + ε) * T ^ (9999999 / 10000000 : ℝ)) := by
  let B := SchwartzMap.seminorm ℝ 0 0 Φ * (Real.sqrt H + 1) * Real.sqrt 2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hk := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 9999999 / 10000000)).eventually_ge_atTop (2 * B / ε)
  filter_upwards [squarefree_coefficient_budget C₀ ε hε, hk, eventually_ge_atTop (1 : ℝ)] with T hbudget hlarge hT
  intro P hP M S u hM hcard hS hu huU D a θ R v c hR hv hc hscale
  let K := T ^ (9999999 / 10000000 : ℝ)
  have hconst : B ≤ Real.exp (ε / 2 * K) := by
    have hh := (div_le_iff₀ hε).mp hlarge
    have he := Real.add_one_le_exp (ε / 2 * K)
    nlinarith
  have hpoly : (1 + Real.sqrt 2 / 16) ^ P.card ≤ Real.exp (K / 10) :=
    (small_kernel_divisor_product_bound P.card).trans (Real.exp_le_exp.mpr (by linarith))
  have hpoint (s : ℕ) (hs : s ∈ S) :
      ‖∑ U ∈ P.powerset, c U * primeDivisorPositive P hP D a θ Φ R v U s‖ ≤ B * Real.exp (K / 10) := by
    apply (small_divisor_combination_bound P c _ B hB hc _).trans
      (mul_le_mul_of_nonneg_left hpoly hB)
    intro U hU
    exact primeDivisorPositive_small_bound P hP D a θ Φ R v H s hR hv hH
      (Nat.pos_of_ne_zero (hS s hs).1.ne_zero) hΦ (hscale s hs) U (Finset.mem_powerset.mp hU)
  have hsum := hbudget M S u hM hS hu huU
  have hsqrt : Real.sqrt (∑ s ∈ S, u ^ s.primeFactors.card / (s : ℝ)) ≤ Real.exp (ε / 2 * K) := by
    apply (Real.sqrt_le_sqrt hsum).trans_eq
    rw [← Real.exp_half]
    congr 1
    ring
  apply (sqrt_weighted_energy_le_uniform S (fun s => u ^ s.primeFactors.card / (s : ℝ)) _
    (B * Real.exp (K / 10)) (by positivity) (fun _ _ => by positivity) hpoint).trans
  calc
    _ ≤ (Real.exp (ε / 2 * K) * Real.exp (K / 10)) * Real.exp (ε / 2 * K) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hconst (Real.exp_nonneg _)) hsqrt
        (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

end Ostmann

end OAI
