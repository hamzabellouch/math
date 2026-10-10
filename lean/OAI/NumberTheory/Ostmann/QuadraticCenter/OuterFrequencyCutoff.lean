import OAI.NumberTheory.Ostmann.Construction.OriginalKernelDecomposition

namespace OAI

/-! # Large outer divisors vanish in the original compactly supported series -/

namespace Ostmann

open scoped BigOperators SchwartzMap

theorem positiveQuadraticSum_zero_above_base {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (a : ZMod q) (θ : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (R v H : ℝ) (s : ℕ) (hR : 0 < R) (hv : 1 ≤ v)
    (hs : H * R * q < s) (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    positiveQuadraticSum g a θ Φ R v s = 0 := by
  unfold positiveQuadraticSum
  have hz (w : ℕ) : (if 0 < w then quadraticDensityTerm g a θ Φ R v s w else 0) = 0 := by
    split_ifs with hw
    · have hwR : (1 : ℝ) ≤ w := by exact_mod_cast hw
      have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
      have hfactor : 1 ≤ v * (w : ℝ) ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_left hv (sq_nonneg (w : ℝ))]
      have hbase : (s : ℝ) ≤ (s : ℝ) * v * (w : ℝ) ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_left hfactor (Nat.cast_nonneg (α := ℝ) s)]
      have harg : H < (s : ℝ) * v * (w : ℝ) ^ 2 / (R * q) := by
        apply (lt_div_iff₀ (mul_pos hR hq)).mpr
        nlinarith
      simp only [quadraticDensityTerm, hΦ _ harg, mul_zero]
    · rfl
  simp only [hz, tsum_zero, mul_zero]

theorem primeDivisorMultiples_zero_above_base (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (U V : Finset ℕ) (hU : U ⊆ Q) (hV : V ⊆ Q)
    (a : ∀ W : Finset ℕ, ZMod W.toList.prod) (θ : Finset ℕ → ℝ)
    (Φ : 𝓢(ℝ, ℂ)) (R H : ℝ) (s P N : ℕ)
    (hR : 0 < R) (hH : 0 ≤ H) (hs : 1 ≤ s)
    (hcut : H * R * Q.toList.prod ≤ N) (hP : N < P ^ 2)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    primeDivisorMultiples Q hQ D a θ Φ R V.toList.prod P U s = 0 := by
  let : NeZero U.toList.prod := ⟨(prime_list_prod_pos _
    (primeSet_list_prime U (fun p hp => hQ p (hU hp)))).ne'⟩
  have hv : 1 ≤ (V.toList.prod : ℝ) := by
    exact_mod_cast prime_list_prod_pos _ (primeSet_list_prime V (fun p hp => hQ p (hV hp)))
  have hcutU : H * R * U.toList.prod ≤ N :=
    (mul_le_mul_of_nonneg_left
      (Nat.cast_le.mpr (primeSet_prod_le_of_subset Q U hQ hU)) (mul_nonneg hH hR.le)).trans hcut
  have hbase : H * R * U.toList.prod < ((s * P ^ 2 : ℕ) : ℝ) := by
    have hn : (N : ℝ) < (P ^ 2 : ℕ) := by exact_mod_cast hP
    have hs' : P ^ 2 ≤ s * P ^ 2 := Nat.le_mul_of_pos_left _ hs
    exact hcutU.trans_lt (hn.trans_le (Nat.cast_le.mpr hs'))
  simp only [primeDivisorMultiples, primeDivisorPositive, dite_eq_left hU]
  rw [positiveQuadraticSum_zero_above_base _ _ _ Φ R V.toList.prod H (s * P ^ 2)
    hR hv hbase hΦ, mul_zero]

theorem arithmeticQuadraticCoefficient_zero_outer (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (M N P s h₀ : ℕ)
    (θ R H : ℝ) (Φ : 𝓢(ℝ, ℂ)) (hR : 0 < R) (hH : 0 ≤ H) (hs : 1 ≤ s)
    (hcut : H * R * Q.toList.prod ≤ N) (hP : N < P ^ 2)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    arithmeticQuadraticCoefficient Q hQ D Φ R P M h₀ θ s = 0 := by
  unfold arithmeticQuadraticCoefficient fullQuadraticCoefficient divisorWeightedCoefficient
  apply Finset.sum_eq_zero
  intro V hV
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro U hU
  rw [primeDivisorMultiples_zero_above_base Q hQ D U V
    (Finset.mem_powerset.mp hU) (Finset.mem_powerset.mp hV) _ _ Φ R H s P N
      hR hH hs hcut hP hΦ, mul_zero]

theorem quadraticArrayStatistic_zero_outer (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (D : ∀ p : ℕ, Finset (ZMod p)) (M N P h₀ : ℕ)
    (θ R H : ℝ) (Φ : 𝓢(ℝ, ℂ)) (S : Finset ℕ)
    (hR : 0 < R) (hH : 0 ≤ H) (hS : ∀ s ∈ S, 1 ≤ s)
    (hcut : H * R * Q.toList.prod ≤ N) (hP : N < P ^ 2)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    quadraticArrayStatistic S M (arithmeticQuadraticCoefficient Q hQ D Φ R P M h₀ θ) = 0 := by
  rw [quadraticArrayStatistic_finset]
  apply Finset.sum_eq_zero
  intro s hs
  rw [arithmeticQuadraticCoefficient_zero_outer Q hQ D M N P s h₀ θ R H Φ
    hR hH (hS s hs) hcut hP hΦ, mul_zero, zero_mul]

end Ostmann

end OAI
