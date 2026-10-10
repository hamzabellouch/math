import OAI.NumberTheory.EgyptianFractions.RationalDivisorSupplyAlgebra

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- Dividing a rational-divisor representation by a positive integer does not
change its numerators or its number of summands. -/
theorem HasRationalDivisorSum.div_nat {K B : ℕ} {x : ℚ}
    (h : HasRationalDivisorSum K x B) {d : ℕ} (hd : 0 < d) :
    HasRationalDivisorSum K (x / (d : ℚ)) B := by
  obtain ⟨k, hk, e, t, het, hsum⟩ := h
  refine ⟨k, hk, e, (fun i => t i * d), ?_, ?_⟩
  · intro i
    exact ⟨(het i).1, (het i).2.1, Nat.mul_pos (het i).2.2 hd⟩
  · simp only [Nat.cast_mul, ← div_div]
    rw [← Finset.sum_div, hsum]

/-- It suffices to represent any positive integral multiple of the desired
integer. No upper bound on the multiplier is needed in this algebraic step. -/
theorem HasRationalDivisorSum.of_nat_multiple {K B d s : ℕ}
    (h : HasRationalDivisorSum K ((d * s : ℕ) : ℚ) B) (hd : 0 < d) :
    HasRationalDivisorSum K (s : ℚ) B := by
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  simpa only [Nat.cast_mul, mul_div_cancel_left₀ _ hdq] using h.div_nat hd

/-- Finite sums combine rational-divisor representations with the exact sum
of their budgets, without requiring the displayed summands to be distinct. -/
theorem HasRationalDivisorSum.finset_sum {ι : Type*} {K : ℕ}
    (I : Finset ι) (x : ι → ℚ) (B : ι → ℕ)
    (h : ∀ i ∈ I, HasRationalDivisorSum K (x i) (B i)) :
    HasRationalDivisorSum K (∑ i ∈ I, x i) (∑ i ∈ I, B i) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
      refine ⟨0, by simp, Fin.elim0, Fin.elim0, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · simp
  | @insert a I ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (h a (Finset.mem_insert_self a I)).add
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- Uniform-budget version for a finite indexed family. -/
theorem HasRationalDivisorSum.sum_fin {K B n : ℕ} {x : Fin n → ℚ}
    (h : ∀ i, HasRationalDivisorSum K (x i) B) :
    HasRationalDivisorSum K (∑ i, x i) (n * B) := by
  simpa using HasRationalDivisorSum.finset_sum
    (K := K) Finset.univ x (fun _ => B) (fun i _ => h i)

/-- A positive integer sum divisible by `s` gives a rational representation
of `s` with the same supply and budget. This is the precise positive-multiple
interface; in particular its arithmetic premise is not an exact-sum premise. -/
theorem rational_divisor_sum_of_dvd_sum {K B n s : ℕ} (a : Fin n → ℕ)
    (hrep : ∀ i, HasRationalDivisorSum K (a i : ℚ) B)
    (hpos : 0 < ∑ i, a i) (hdiv : s ∣ ∑ i, a i) :
    HasRationalDivisorSum K (s : ℚ) (n * B) := by
  obtain ⟨d, hd⟩ := hdiv
  have hdpos : 0 < d := by
    by_contra hn
    have hd0 : d = 0 := by omega
    have hz : (∑ i, a i) = 0 := by simpa only [hd0, Nat.mul_zero] using hd
    exact (Nat.ne_of_gt hpos) hz
  have hsum : HasRationalDivisorSum K ((d * s : ℕ) : ℚ) (n * B) := by
    have h := HasRationalDivisorSum.sum_fin hrep
    rw [← Nat.cast_sum, hd, Nat.mul_comm s d] at h
    exact h
  exact hsum.of_nat_multiple hdpos

/-- Each half of a represented pair has the same two-summand budget.
This is the scaling step for a half-Goldbach additive basis. -/
theorem rational_divisor_sum_of_half_pair {K B p q s : ℕ}
    (hp : HasRationalDivisorSum K (p : ℚ) B)
    (hq : HasRationalDivisorSum K (q : ℚ) B)
    (hs : 2 * s = p + q) :
    HasRationalDivisorSum K (s : ℚ) (2 * B) := by
  have h : HasRationalDivisorSum K ((2 * s : ℕ) : ℚ) (B + B) := by
    rw [hs, Nat.cast_add]
    exact hp.add hq
  simpa only [two_mul] using h.of_nat_multiple (by norm_num : 0 < 2)

/-- A sum of `n` members of a half-pair set lifts to a representation of its
sum with `2*n*B` rational divisors. All prime or density information belongs
in the explicit hypotheses supplied to this elementary statement. -/
theorem rational_divisor_sum_of_half_pair_basis {K B n s : ℕ}
    (a p q : Fin n → ℕ) (hs : ∑ i, a i = s)
    (ha : ∀ i, 2 * a i = p i + q i)
    (hp : ∀ i, HasRationalDivisorSum K (p i : ℚ) B)
    (hq : ∀ i, HasRationalDivisorSum K (q i : ℚ) B) :
    HasRationalDivisorSum K (s : ℚ) (2 * n * B) := by
  have h := HasRationalDivisorSum.sum_fin
    (fun i => rational_divisor_sum_of_half_pair (hp i) (hq i) (ha i))
  rw [← Nat.cast_sum, hs] at h
  convert h using 1
  ring

end Problem337

end

end OAI
