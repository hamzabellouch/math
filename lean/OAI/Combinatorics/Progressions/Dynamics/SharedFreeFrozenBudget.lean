import OAI.Combinatorics.Progressions.Estimates.SharedFreeFrozenComparison

namespace OAI

section

namespace Erdos3

theorem exists_sharedFreeFrozenComparisonBudget_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ q p pF : ℝ, 0 ≤ q → q ≤ p → 0 ≤ p → p ≤ pF →
      let p₁ := sharedFreeFrozenCoverBudget s pF
      let q₁ := p₁ + sharedFreeComparisonBasisBudget q p + 2
      p₁ ≤ (pF + C) ^ C ∧
      (q₁ + nativePairModelConstant s) ^ nativePairModelConstant s ≤ (pF + C) ^ C ∧
      nativeLowerPairModelBudget s q₁ ≤ (pF + C) ^ C := by
  obtain ⟨b, _, hb⟩ := exists_sharedFreeComparisonBasisBudget_bound
  obtain ⟨c, _, hc⟩ := exists_nativeLowerPairModelBudget_bound s
  let a := (RationalFilteredNilmanifold.exists_shared_frozen_unit_observable.{0, 0, 0} s 1).choose
  let A : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  let Q : Polynomial ℕ := A + (Polynomial.X + Polynomial.C b) ^ b + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (A + (Q + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro q p pF hq hqp hp hppF p₁ q₁
  have hpF : 0 ≤ pF := hp.trans hppF
  have hp₁ : 0 ≤ p₁ := by
    change 0 ≤ (pF + a) ^ a
    positivity
  have hB := sharedFreeComparisonBasisBudget_nonneg hq hp
  have hq₁ : 0 ≤ q₁ := by dsimp only [q₁]; positivity
  let v := p₁ + (pF + b) ^ b + 2
  have hqv : q₁ ≤ v := by
    have hbb : sharedFreeComparisonBasisBudget q p ≤ (pF + b) ^ b :=
      (hb q p hq hqp hp).trans
        (pow_le_pow_left₀ (by positivity : 0 ≤ p + b)
          (show p + b ≤ pF + b by linarith) b)
    dsimp only [q₁, v]
    linarith
  have hv : 0 ≤ v := hq₁.trans hqv
  have hsum : p₁ + (v + c) ^ c ≤ (pF + C) ^ C := by
    change (pF + a) ^ a + ((pF + a) ^ a + (pF + b) ^ b + 2 + c) ^ c ≤ (pF + C) ^ C
    simpa [A, Q, Polynomial.eval₂_pow] using hbudget pF hpF
  have htail : (v + c) ^ c ≤ (pF + C) ^ C := (le_add_of_nonneg_left hp₁).trans hsum
  have hfirst : p₁ ≤ (pF + C) ^ C :=
    (le_add_of_nonneg_right (by positivity : 0 ≤ (v + c) ^ c)).trans hsum
  have hpow : (q₁ + c) ^ c ≤ (v + c) ^ c :=
    pow_le_pow_left₀ (by positivity) (by linarith) c
  exact ⟨hfirst, (hc q₁ hq₁).1.trans (hpow.trans htail),
    (hc q₁ hq₁).2.trans (hpow.trans htail)⟩

end Erdos3

end

end OAI
