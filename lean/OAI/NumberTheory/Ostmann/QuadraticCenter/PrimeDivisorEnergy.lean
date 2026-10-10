import OAI.NumberTheory.Ostmann.QuadraticCenter.PrimeSetQuadratic

namespace OAI

/-! # The low-weight coefficient energy of the actual divisor sums -/

namespace Ostmann

open scoped BigOperators ComplexConjugate SchwartzMap

noncomputable def primeDivisorQuadratic (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (S : ∀ p : ℕ, Finset (ZMod p)) (W : Finset ℕ → Finset ℕ)
    (a : ∀ U : Finset ℕ, ZMod U.toList.prod) (θ : Finset ℕ → ℝ)
    (Φ : 𝓢(ℝ, ℂ)) (R v : ℝ) (U : Finset ℕ) (s : ℕ) : ℂ := by
  classical
  exact if hU : U ⊆ P then
    primeSetQuadraticSum U (fun p hp => hP p (hU hp)) S (W U) (a U) (θ U) Φ R v s
  else 0

theorem primeDivisorQuadratic_pair (P U V : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hU : U ⊆ P) (hV : V ⊆ P)
    (S : ∀ p : ℕ, Finset (ZMod p)) (W : Finset ℕ → Finset ℕ)
    (a : ∀ U : Finset ℕ, ZMod U.toList.prod) (θ : Finset ℕ → ℝ)
    (Φ : 𝓢(ℝ, ℂ)) (R v C : ℝ) (M N : ℕ)
    (hR : 0 < R) (hv : 0 < v) (hC : 0 ≤ C) (hM : 0 < M) (hN : 0 < N)
    (hperiod : P.toList.prod ^ 2 ≤ N)
    (hW : ∀ Q ⊆ P, ∀ w ∈ W Q,
      0 < w ∧ (w : ℝ) ^ 2 ≤ C * R * Q.toList.prod / ((N : ℝ) * v)) :
    ‖∑ n ∈ Finset.range N, (1 / ((n + M : ℕ) : ℝ) : ℂ) *
      (primeDivisorQuadratic P hP S W a θ Φ R v U (n + M) *
        conj (primeDivisorQuadratic P hP S W a θ Φ R v V (n + M)))‖ ≤
      C * (4 * correlationWeightBudget Φ Φ C C) *
        ∏ p ∈ P, if (p ∈ U ↔ p ∈ V) then 1 else (Real.sqrt (p : ℝ))⁻¹ := by
  have hb := primeSet_quadratic_correlation P U V hP hU hV S (W U) (W V)
    (a U) (a V) Φ Φ (θ U) (θ V) R v C M N hR hv hC hM hN hperiod (hW U hU) (hW V hV)
  have heq : (∑ n ∈ Finset.range N, (1 / ((n + M : ℕ) : ℝ) : ℂ) *
      (primeDivisorQuadratic P hP S W a θ Φ R v U (n + M) *
        conj (primeDivisorQuadratic P hP S W a θ Φ R v V (n + M)))) =
      ∑ n ∈ Finset.range N,
        primeSetQuadraticSum U (fun p hp => hP p (hU hp)) S (W U) (a U) (θ U) Φ R v (n + M) *
        conj (primeSetQuadraticSum V (fun p hp => hP p (hV hp)) S (W V) (a V) (θ V) Φ R v (n + M)) /
          ((n + M : ℕ) : ℂ) := by
    apply Finset.sum_congr rfl
    intro n hn
    simp only [primeDivisorQuadratic, dite_eq_left hU, dite_eq_left hV,
      Complex.ofReal_natCast]
    ring
  rw [heq]
  exact hb

/-- The unweighted coefficient-energy bound obtained from double-divisor
correlations for the quadratic family. -/
theorem primeDivisor_quadratic_energy (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (S : ∀ p : ℕ, Finset (ZMod p)) (W : Finset ℕ → Finset ℕ)
    (a : ∀ U : Finset ℕ, ZMod U.toList.prod) (θ : Finset ℕ → ℝ)
    (Φ : 𝓢(ℝ, ℂ)) (R v C lam : ℝ) (M N : ℕ) (c : Finset ℕ → ℂ)
    (hR : 0 < R) (hv : 0 < v) (hC : 0 ≤ C) (hlam : 0 ≤ lam)
    (hM : 0 < M) (hN : 0 < N) (hperiod : P.toList.prod ^ 2 ≤ N)
    (hW : ∀ Q ⊆ P, ∀ w ∈ W Q,
      0 < w ∧ (w : ℝ) ^ 2 ≤ C * R * Q.toList.prod / ((N : ℝ) * v))
    (hc : ∀ U ∈ P.powerset, ‖c U‖ ≤ lam ^ U.card) :
    (∑ n ∈ Finset.range N, (1 / ((n + M : ℕ) : ℝ)) *
      ‖∑ U ∈ P.powerset, c U * primeDivisorQuadratic P hP S W a θ Φ R v U (n + M)‖ ^ 2) ≤
      (C * (4 * correlationWeightBudget Φ Φ C C)) *
        ∏ p ∈ P, (1 + lam ^ 2 + 2 * lam * (Real.sqrt (p : ℝ))⁻¹) := by
  refine divisor_combination_energy_bound (Finset.range N) P
    (fun n => 1 / ((n + M : ℕ) : ℝ)) c
    (fun U n => primeDivisorQuadratic P hP S W a θ Φ R v U (n + M))
    lam (C * (4 * correlationWeightBudget Φ Φ C C)) hlam ?_ hc ?_
  · unfold correlationWeightBudget
    positivity
  · intro U hU V hV
    simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_natCast] using
      primeDivisorQuadratic_pair P U V hP (Finset.mem_powerset.mp hU)
      (Finset.mem_powerset.mp hV) S W a θ Φ R v C M N hR hv hC hM hN hperiod hW

/-- Low-weight indices may be restricted arbitrarily; positivity extends the
underlying energy to the full interval before the divisor expansion. -/
theorem primeDivisor_low_weight_energy (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hlarge : ∀ p ∈ P, 10000 ≤ p)
    (S : ∀ p : ℕ, Finset (ZMod p)) (W : Finset ℕ → Finset ℕ)
    (a : ∀ U : Finset ℕ, ZMod U.toList.prod) (θ : Finset ℕ → ℝ)
    (Φ : 𝓢(ℝ, ℂ)) (R v C u K : ℝ) (M N : ℕ) (c : Finset ℕ → ℂ) (F : Finset ℕ)
    (hK : (P.card : ℝ) ≤ K)
    (hR : 0 < R) (hv : 0 < v) (hC : 0 ≤ C) (hM : 0 < M) (hN : 0 < N)
    (hperiod : P.toList.prod ^ 2 ≤ N)
    (hW : ∀ Q ⊆ P, ∀ w ∈ W Q,
      0 < w ∧ (w : ℝ) ^ 2 ≤ C * R * Q.toList.prod / ((N : ℝ) * v))
    (hc : ∀ U ∈ P.powerset, ‖c U‖ ≤ (1 / 16 : ℝ) ^ U.card)
    (hF : F ⊆ Finset.range N)
    (hweight : ∀ n ∈ F, u ^ (n + M).primeFactors.card ≤ Real.exp (K / 200)) :
    (∑ n ∈ F, (u ^ (n + M).primeFactors.card / ((n + M : ℕ) : ℝ)) *
      ‖∑ U ∈ P.powerset, c U * primeDivisorQuadratic P hP S W a θ Φ R v U (n + M)‖ ^ 2) ≤
      (C * (4 * correlationWeightBudget Φ Φ C C)) * Real.exp (3 * K / 250) := by
  let G := fun n => ∑ U ∈ P.powerset, c U * primeDivisorQuadratic P hP S W a θ Φ R v U (n + M)
  have hbase := primeDivisor_quadratic_energy P hP S W a θ Φ R v C (1 / 16) M N c
    hR hv hC (by norm_num) hM hN hperiod hW hc
  have hB : 0 ≤ C * (4 * correlationWeightBudget Φ Φ C C) := by
    unfold correlationWeightBudget
    positivity
  calc
    _ ≤ ∑ n ∈ F, Real.exp (K / 200) *
        ((1 / ((n + M : ℕ) : ℝ)) * ‖G n‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro n hn
      have hh := mul_le_mul_of_nonneg_right (hweight n hn)
        (show 0 ≤ (1 / ((n + M : ℕ) : ℝ)) * ‖G n‖ ^ 2 by positivity)
      convert hh using 1
      ring
    _ ≤ Real.exp (K / 200) *
        ∑ n ∈ Finset.range N, (1 / ((n + M : ℕ) : ℝ)) * ‖G n‖ ^ 2 := by
      rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      exact Finset.sum_le_sum_of_subset_of_nonneg hF (fun _ _ _ => by positivity)
    _ ≤ Real.exp (K / 200) *
        ((C * (4 * correlationWeightBudget Φ Φ C C)) *
          ∏ p ∈ P, (1 + (1 / 16 : ℝ) ^ 2 + 2 * (1 / 16 : ℝ) * (Real.sqrt (p : ℝ))⁻¹)) :=
      mul_le_mul_of_nonneg_left hbase (Real.exp_nonneg _)
    _ = (C * (4 * correlationWeightBudget Φ Φ C C)) *
        (Real.exp (K / 200) *
          ∏ p ∈ P, (1 + (1 / 16 : ℝ) ^ 2 + 2 * (1 / 16 : ℝ) * (Real.sqrt (p : ℝ))⁻¹)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (low_weight_euler_bound_scale P hlarge K hK) hB

end Ostmann

end OAI
