import OAI.NumberTheory.TwoPoint.Walks.TuplePrimeCosts
import OAI.NumberTheory.TwoPoint.Bounds.PaddingDefectMass

namespace OAI

/-! The tensor product of the tuple and padding laws retains separate first
moments, rather than the largest prime cost of an individual divisor. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma pair_prime_cost_sum (D Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (hcop : ∀ d ∈ D, ∀ q ∈ retainedPrimeDivisors Q, d.Coprime q)
    (c : ℕ → ℝ) :
    (∑ d ∈ D, ∑ q ∈ retainedPrimeDivisors Q,
      (4 : ℝ) ^ q.primeFactors.card / (d * q : ℕ) *
        ∑ p ∈ (d * q).primeFactors, c p) =
      paddingTiltNormalizer Q * (∑ d ∈ D, (1 / (d : ℝ)) * ∑ p ∈ d.primeFactors, c p) +
      (∑ d ∈ D, 1 / (d : ℝ)) * paddingTiltNormalizer Q *
        ∑ p ∈ Q, (4 / ((p : ℝ) + 4)) * c p := by
  have he (d : ℕ) (hd : d ∈ D) :
      (∑ q ∈ retainedPrimeDivisors Q,
        (4 : ℝ) ^ q.primeFactors.card / (d * q : ℕ) *
          ∑ p ∈ (d * q).primeFactors, c p) =
        (1 / (d : ℝ)) * (∑ p ∈ d.primeFactors, c p) * paddingTiltNormalizer Q +
        (1 / (d : ℝ)) * (paddingTiltNormalizer Q *
          ∑ p ∈ Q, (4 / ((p : ℝ) + 4)) * c p) := by
    calc
      _ = ∑ q ∈ retainedPrimeDivisors Q,
          (((1 / (d : ℝ)) * (∑ p ∈ d.primeFactors, c p)) *
            ((4 : ℝ) ^ q.primeFactors.card / (q : ℝ)) +
          (1 / (d : ℝ)) * (((4 : ℝ) ^ q.primeFactors.card / (q : ℝ)) *
            ∑ p ∈ q.primeFactors, c p)) := by
        apply sum_congr rfl
        intro q hq
        rw [(hcop d hd q hq).primeFactors_mul,
          sum_union (hcop d hd q hq).disjoint_primeFactors, Nat.cast_mul]
        ring
      _ = _ := by
        rw [sum_add_distrib, ← mul_sum, ← mul_sum,
          ← paddingTiltNormalizer_eq_divisor_sum Q hQ, padding_prime_cost_sum Q hQ]
  calc
    _ = ∑ d ∈ D, ((1 / (d : ℝ)) * (∑ p ∈ d.primeFactors, c p) * paddingTiltNormalizer Q +
        (1 / (d : ℝ)) * (paddingTiltNormalizer Q *
          ∑ p ∈ Q, (4 / ((p : ℝ) + 4)) * c p)) := by
      apply sum_congr rfl
      intro d hd
      exact he d hd
    _ = _ := by
      rw [sum_add_distrib, ← sum_mul, ← sum_mul]
      ring

lemma tuple_padding_coprime {J : ℕ} (P : Fin J → Finset ℕ) (Q : Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (hQ : ∀ p ∈ Q, p.Prime) (hPQ : Disjoint (primeTuplePool P) Q)
    {d q : ℕ} (hd : d ∈ primeTupleDivisors P) (hq : q ∈ retainedPrimeDivisors Q) :
    d.Coprime q := by
  apply Nat.coprime_of_dvd
  intro p hp hpd hpq
  have hd0 : d ≠ 0 := (primeTupleDivisors_arithmetic P hprime hdisjoint hd).1.ne_zero
  have hq0 : q ≠ 0 := (retainedPrimeDivisor_pos Q hQ hq).ne'
  have hpD : p ∈ d.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpd, hd0⟩
  have hpQ : p ∈ q.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpq, hq0⟩
  exact disjoint_left.mp hPQ
    ((primeTupleDivisors_arithmetic P hprime hdisjoint hd).2.2 hpD)
    (retainedPrimeDivisor_factors Q hQ hq hpQ)

lemma tuple_padding_prime_cost_bound {J : ℕ} (P : Fin J → Finset ℕ) (Q : Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j k, k ≠ j → Disjoint (P j) (P k))
    (hQ : ∀ p ∈ Q, p.Prime) (hPQ : Disjoint (primeTuplePool P) Q)
    (c : ℕ → ℝ) (hc : ∀ p ∈ primeTuplePool P, 0 ≤ c p)
    (W : ℝ) (hW : 0 < W) (hmass : ∀ j, W ≤ primeHarmonicMass (P j)) :
    (∑ d ∈ primeTupleDivisors P, ∑ q ∈ retainedPrimeDivisors Q,
      (4 : ℝ) ^ q.primeFactors.card / (d * q : ℕ) *
        ∑ p ∈ (d * q).primeFactors, c p) ≤
      paddingTiltNormalizer Q * (∏ j, primeHarmonicMass (P j)) *
        ((∑ p ∈ primeTuplePool P, c p / (p : ℝ)) / W +
          ∑ p ∈ Q, (4 / ((p : ℝ) + 4)) * c p) := by
  rw [pair_prime_cost_sum _ Q hQ
    (fun _ hd _ hq => tuple_padding_coprime P Q hprime hdisjoint hQ hPQ hd hq) c]
  have hm : (∑ d ∈ primeTupleDivisors P, 1 / (d : ℝ)) =
      ∏ j, primeHarmonicMass (P j) := by
    rw [primeTupleDivisors_mass P hprime hdisjoint]
    simp only [primeHarmonicMass_eq_sum]
  rw [hm]
  have hb := mul_le_mul_of_nonneg_left
    (primeTupleDivisors_cost_bound P hprime hdisjoint c hc W hW hmass)
    (paddingTiltNormalizer_pos Q).le
  apply (add_le_add hb (le_refl _)).trans_eq
  ring

end TwoPointCorrelations

end OAI
