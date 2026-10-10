import OAI.NumberTheory.JointDickman.Arithmetic.PrimeIndicatorErrors
import OAI.NumberTheory.JointDickman.Amplification.TailViolationSum

namespace OAI

/-! # Actual prefix and tail violation probabilities -/

namespace JointDickman

open Finset

private theorem primePrefix_of_subset {S P : Finset ℕ} (hS : S ⊆ P) (B : ℕ) (g : ℝ) :
    primePrefix B g S = S ∩ primePrefix B g P := by
  simpa only [inter_eq_left.mpr hS] using primePrefix_inter B g S P

private theorem primeTail_of_subset {S P : Finset ℕ} (hS : S ⊆ P) (Y : ℝ) :
    S.filter (fun p : ℕ => Y < Real.log p) = S ∩ P.filter (fun p : ℕ => Y < Real.log p) := by
  ext p
  simp only [mem_filter, mem_inter]
  exact ⟨fun h => ⟨h.1, hS h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩

theorem bernoulli_strict_lower_tail (B : ℕ) (Q : Finset ℕ) (q : ℕ → ℝ)
    (s r : ℝ) {D : ℝ} (hP : 6 ≤ auxiliaryCutoff B) (hD : 0 ≤ D)
    (hq : ∀ p ∈ auxiliaryPrimes B, 0 ≤ q p ∧ q p ≤ 1)
    (herr : (∑ p ∈ auxiliaryPrimes B, |q p - (1 / 2 : ℝ) / p|) ≤ D)
    (hs : 0 < s) (he : Real.exp (-s) ≤ 2) :
    (∑ S ∈ (auxiliaryPrimes B).powerset,
      if ((S ∩ Q).card : ℝ) < r then bernoulliSubsetMass (auxiliaryPrimes B) q S else 0) ≤
      Real.exp D * Real.exp (s * r + ((Real.exp (-s) - 1) / 2) *
        tiltPrimeReciprocalMass (auxiliaryCutoff B) (sieveCutoff 4 B) Q) := by
  classical
  have hb := bernoulli_count_tail_stable B Q q (-s) r hP hD hq herr he
  have hc : (∑ S ∈ (auxiliaryPrimes B).powerset,
      if ((S ∩ Q).card : ℝ) < r then bernoulliSubsetMass (auxiliaryPrimes B) q S else 0) ≤
      ∑ S ∈ (auxiliaryPrimes B).powerset,
        if -s * r ≤ -s * (S ∩ Q).card then bernoulliSubsetMass (auxiliaryPrimes B) q S else 0 := by
    apply sum_le_sum
    intro S hS
    have hw := bernoulliSubsetMass_nonneg (mem_powerset.mp hS) hq
    split_ifs with h h' h'
    · exact le_rfl
    · exfalso
      exact h' (by nlinarith only [h, hs])
    · exact hw
    · exact le_rfl
  simpa only [neg_neg] using hc.trans hb

theorem bernoulli_strict_upper_tail (B : ℕ) (Q : Finset ℕ) (q : ℕ → ℝ)
    (s r : ℝ) {D : ℝ} (hP : 6 ≤ auxiliaryCutoff B) (hD : 0 ≤ D)
    (hq : ∀ p ∈ auxiliaryPrimes B, 0 ≤ q p ∧ q p ≤ 1)
    (herr : (∑ p ∈ auxiliaryPrimes B, |q p - (1 / 2 : ℝ) / p|) ≤ D)
    (hs : 0 < s) (he : Real.exp s ≤ 2) :
    (∑ S ∈ (auxiliaryPrimes B).powerset,
      if r < ((S ∩ Q).card : ℝ) then bernoulliSubsetMass (auxiliaryPrimes B) q S else 0) ≤
      Real.exp D * Real.exp (-s * r + ((Real.exp s - 1) / 2) *
        tiltPrimeReciprocalMass (auxiliaryCutoff B) (sieveCutoff 4 B) Q) := by
  classical
  apply LE.le.trans _ (bernoulli_count_tail_stable B Q q s r hP hD hq herr he)
  apply sum_le_sum
  intro S hS
  have hw := bernoulliSubsetMass_nonneg (mem_powerset.mp hS) hq
  split_ifs with h h' h'
  · exact le_rfl
  · exfalso
    exact h' (by nlinarith only [h, hs])
  · exact hw
  · exact le_rfl

theorem bernoulli_prefix_lower_bound (B : ℕ) (q : ℕ → ℝ) (g τ s : ℝ) {D : ℝ}
    (hP : 6 ≤ auxiliaryCutoff B) (hD : 0 ≤ D)
    (hq : ∀ p ∈ auxiliaryPrimes B, 0 ≤ q p ∧ q p ≤ 1)
    (herr : (∑ p ∈ auxiliaryPrimes B, |q p - (1 / 2 : ℝ) / p|) ≤ D)
    (hs : 0 < s) (he : Real.exp (-s) ≤ 2) :
    (∑ S ∈ (auxiliaryPrimes B).powerset,
      if ((primePrefix B g S).card : ℝ) < (g / 2 - τ) * auxiliaryLogLength B
      then bernoulliSubsetMass (auxiliaryPrimes B) q S else 0) ≤
      Real.exp D * prefixLowerFactor B 4 g τ s := by
  classical
  have hb := bernoulli_strict_lower_tail B (primePrefix B g (auxiliaryPrimes B)) q
    s ((g / 2 - τ) * auxiliaryLogLength B) hP hD hq herr hs he
  have heq : (∑ S ∈ (auxiliaryPrimes B).powerset,
      if ((primePrefix B g S).card : ℝ) < (g / 2 - τ) * auxiliaryLogLength B
      then bernoulliSubsetMass (auxiliaryPrimes B) q S else 0) =
      ∑ S ∈ (auxiliaryPrimes B).powerset,
      if ((S ∩ primePrefix B g (auxiliaryPrimes B)).card : ℝ) < (g / 2 - τ) * auxiliaryLogLength B
      then bernoulliSubsetMass (auxiliaryPrimes B) q S else 0 := by
    apply sum_congr rfl
    intro S hS
    rw [primePrefix_of_subset (mem_powerset.mp hS)]
  rw [heq]
  simpa only [prefixLowerFactor, mul_assoc] using hb

theorem bernoulli_prefix_upper_bound (B : ℕ) (q : ℕ → ℝ) (g τ s : ℝ) {D : ℝ}
    (hP : 6 ≤ auxiliaryCutoff B) (hD : 0 ≤ D)
    (hq : ∀ p ∈ auxiliaryPrimes B, 0 ≤ q p ∧ q p ≤ 1)
    (herr : (∑ p ∈ auxiliaryPrimes B, |q p - (1 / 2 : ℝ) / p|) ≤ D)
    (hs : 0 < s) (he : Real.exp s ≤ 2) :
    (∑ S ∈ (auxiliaryPrimes B).powerset,
      if (g / 2 + τ) * auxiliaryLogLength B < ((primePrefix B g S).card : ℝ)
      then bernoulliSubsetMass (auxiliaryPrimes B) q S else 0) ≤
      Real.exp D * prefixUpperFactor B 4 g τ s := by
  classical
  have hb := bernoulli_strict_upper_tail B (primePrefix B g (auxiliaryPrimes B)) q
    s ((g / 2 + τ) * auxiliaryLogLength B) hP hD hq herr hs he
  have heq : (∑ S ∈ (auxiliaryPrimes B).powerset,
      if (g / 2 + τ) * auxiliaryLogLength B < ((primePrefix B g S).card : ℝ)
      then bernoulliSubsetMass (auxiliaryPrimes B) q S else 0) =
      ∑ S ∈ (auxiliaryPrimes B).powerset,
      if (g / 2 + τ) * auxiliaryLogLength B < ((S ∩ primePrefix B g (auxiliaryPrimes B)).card : ℝ)
      then bernoulliSubsetMass (auxiliaryPrimes B) q S else 0 := by
    apply sum_congr rfl
    intro S hS
    rw [primePrefix_of_subset (mem_powerset.mp hS)]
  rw [heq]
  simpa only [prefixUpperFactor, mul_assoc] using hb

theorem bernoulli_tail_violation_bound (B i : ℕ) (q : ℕ → ℝ) (C : ℝ) {D : ℝ}
    (hP : 6 ≤ auxiliaryCutoff B) (hD : 0 ≤ D)
    (hq : ∀ p ∈ auxiliaryPrimes B, 0 ≤ q p ∧ q p ≤ 1)
    (herr : (∑ p ∈ auxiliaryPrimes B, |q p - (1 / 2 : ℝ) / p|) ≤ D) :
    (∑ S ∈ (auxiliaryPrimes B).powerset,
      if ((S.filter (fun p : ℕ => primeTailEndpoint B i < Real.log p)).card : ℝ) <
        (2 / 5 : ℝ) * Real.log ((B : ℝ) / primeTailEndpoint B i) - C
      then bernoulliSubsetMass (auxiliaryPrimes B) q S else 0) ≤
      Real.exp D * tailChernoffFactor B i 4 C := by
  classical
  have he : Real.exp (-(1 / 10 : ℝ)) ≤ 2 :=
    (Real.exp_le_exp.mpr (by norm_num : -(1 / 10 : ℝ) ≤ 0)).trans (by norm_num)
  have hb := bernoulli_strict_lower_tail B
    ((auxiliaryPrimes B).filter (fun p : ℕ => primeTailEndpoint B i < Real.log p)) q
    (1 / 10) ((2 / 5 : ℝ) * Real.log ((B : ℝ) / primeTailEndpoint B i) - C)
    hP hD hq herr (by norm_num) he
  have heq : (∑ S ∈ (auxiliaryPrimes B).powerset,
      if ((S.filter (fun p : ℕ => primeTailEndpoint B i < Real.log p)).card : ℝ) <
        (2 / 5 : ℝ) * Real.log ((B : ℝ) / primeTailEndpoint B i) - C
      then bernoulliSubsetMass (auxiliaryPrimes B) q S else 0) =
      ∑ S ∈ (auxiliaryPrimes B).powerset,
      if ((S ∩ (auxiliaryPrimes B).filter (fun p : ℕ => primeTailEndpoint B i < Real.log p)).card : ℝ) <
        (2 / 5 : ℝ) * Real.log ((B : ℝ) / primeTailEndpoint B i) - C
      then bernoulliSubsetMass (auxiliaryPrimes B) q S else 0 := by
    apply sum_congr rfl
    intro S hS
    rw [primeTail_of_subset (mem_powerset.mp hS)]
  rw [heq]
  exact hb

end JointDickman

end OAI
