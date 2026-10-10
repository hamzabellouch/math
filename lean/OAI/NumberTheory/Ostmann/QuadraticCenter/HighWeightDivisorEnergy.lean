import OAI.NumberTheory.Ostmann.QuadraticCenter.HighWeightPrimeSet
import OAI.NumberTheory.Ostmann.QuadraticCenter.PrimeDivisorEnergy

namespace OAI

/-! # Exponentially small high-weight energy of the actual divisor expansion -/

namespace Ostmann

open Filter
open scoped BigOperators ComplexConjugate SchwartzMap

theorem eventual_high_weight_divisor_energy (C₀ : ℝ) :
    ∀ᶠ T : ℝ in atTop, ∀ (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
      (N : ℕ) (S : Finset ℕ) (u : ℝ),
      0 < N → 2 * P.toList.prod ^ 2 ≤ N → (2 * N : ℝ) ≤ Real.exp (C₀ * T) →
      (P.card : ℝ) ≤ T ^ (9999999 / 10000000 : ℝ) →
      (∀ s ∈ S, Squarefree s) → (∀ s ∈ S, s ∈ Finset.Ioc N (2 * N)) →
      (∀ s ∈ S, P.toList.prod.Coprime s) → 2 ≤ u → u ≤ 4 * T ^ (1 / 1000000 : ℝ) →
      (∀ s ∈ S, Real.exp (T ^ (9999999 / 10000000 : ℝ) / 200) < u ^ s.primeFactors.card) →
      ∀ (D : ∀ p : ℕ, Finset (ZMod p)) (W : Finset ℕ → Finset ℕ)
        (a : ∀ U : Finset ℕ, ZMod U.toList.prod) (θ : Finset ℕ → ℝ)
        (Φ : 𝓢(ℝ, ℂ)) (R v H : ℝ) (c : Finset ℕ → ℂ),
      0 < R → 0 < v → 0 ≤ H →
      (∀ U ⊆ P, ∀ w ∈ W U, 0 < w ∧ (w : ℝ) ^ 2 ≤ H * R * U.toList.prod / ((N : ℝ) * v)) →
      (∀ U ∈ P.powerset, ‖c U‖ ≤ (1 / 16 : ℝ) ^ U.card) →
      (∑ s ∈ S, (u ^ s.primeFactors.card / (s : ℝ)) *
        ‖∑ U ∈ P.powerset, c U * primeDivisorQuadratic P hP D W a θ Φ R v U s‖ ^ 2) ≤
        (H * (SchwartzMap.seminorm ℝ 0 0 Φ) ^ 2) *
          Real.exp (-9 * T ^ (9999999 / 10000000 : ℝ)) := by
  filter_upwards [eventual_high_weight_primeSet_correlation C₀,
    eventually_ge_atTop (1 : ℝ)] with T hT hT1
  intro P hP N S u hN hsize hcut hcard hS hrange hcop hu huU hhigh D W a θ Φ R v H c
    hR hv hH hW hc
  let K := T ^ (9999999 / 10000000 : ℝ)
  let B := H * (SchwartzMap.seminorm ℝ 0 0 Φ) ^ 2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hpair (U : Finset ℕ) (hU : U ∈ P.powerset) (V : Finset ℕ) (hV : V ∈ P.powerset) :
      ‖∑ s ∈ S, ((u ^ s.primeFactors.card / (s : ℝ) : ℝ) : ℂ) *
        (primeDivisorQuadratic P hP D W a θ Φ R v U s *
          conj (primeDivisorQuadratic P hP D W a θ Φ R v V s))‖ ≤ B * Real.exp (-10 * K) := by
    have hUP := Finset.mem_powerset.mp hU
    have hVP := Finset.mem_powerset.mp hV
    have hUV : U ∪ V ⊆ P := Finset.union_subset hUP hVP
    have hbound := hT U V (fun p hp => hP p (hUP hp)) (fun p hp => hP p (hVP hp))
      N S u hN
      ((Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (primeSet_prod_le_of_subset P (U ∪ V) hP hUV) 2)).trans hsize)
      hcut hS hrange (fun s hs => (hcop s hs).of_dvd_left (primeSet_prod_dvd_of_subset P (U ∪ V) hUV))
      hu huU hhigh D (W U) (W V) (a U) (a V) Φ Φ (θ U) (θ V) R v H hR hv hH
      (hW U hUP) (hW V hVP)
    have heq : (∑ s ∈ S, ((u ^ s.primeFactors.card / (s : ℝ) : ℝ) : ℂ) *
        (primeDivisorQuadratic P hP D W a θ Φ R v U s *
          conj (primeDivisorQuadratic P hP D W a θ Φ R v V s))) =
        ∑ s ∈ S, (u ^ s.primeFactors.card : ℂ) *
          (primeSetQuadraticSum U (fun p hp => hP p (hUP hp)) D (W U) (a U) (θ U) Φ R v s *
          conj (primeSetQuadraticSum V (fun p hp => hP p (hVP hp)) D (W V) (a V) (θ V) Φ R v s) / (s : ℂ)) := by
      apply Finset.sum_congr rfl
      intro s hs
      simp only [primeDivisorQuadratic, dite_eq_left hUP, dite_eq_left hVP,
        Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_natCast]
      ring
    rw [heq]
    simpa only [B, K, pow_two] using hbound
  have he := uniform_divisor_combination_energy_bound S P
    (fun s => u ^ s.primeFactors.card / (s : ℝ)) c (primeDivisorQuadratic P hP D W a θ Φ R v)
    (1 / 16) (B * Real.exp (-10 * K)) (by norm_num) (by positivity) hc hpair
  have hpow : (1 + (1 / 16 : ℝ)) ^ (2 * P.card) ≤ Real.exp K := by
    calc
      _ ≤ (Real.exp (1 / 16 : ℝ)) ^ (2 * P.card) :=
        pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp (1 / 16 : ℝ)]) _
      _ = Real.exp ((P.card : ℝ) / 8) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
      _ ≤ _ := Real.exp_le_exp.mpr (by
        have hK : 0 ≤ K := by dsimp [K]; positivity
        dsimp [K] at hK ⊢
        linarith)
  calc
    _ ≤ _ := he
    _ ≤ (B * Real.exp (-10 * K)) * Real.exp K := mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = B * Real.exp (-9 * K) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

end Ostmann

end OAI
