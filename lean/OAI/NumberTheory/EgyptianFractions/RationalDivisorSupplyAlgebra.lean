import Mathlib

namespace OAI
noncomputable section

open scoped BigOperators

namespace Problem337

/-- A rational number is a sum of at most `B` positive rational summands,
whose natural numerators divide the fixed common supply `K`. -/
def HasRationalDivisorSum (K : ℕ) (x : ℚ) (B : ℕ) : Prop :=
  ∃ k : ℕ, k ≤ B ∧ ∃ e t : Fin k → ℕ,
    (∀ i, 0 < e i ∧ e i ∣ K ∧ 0 < t i) ∧
    (∑ i, (e i : ℚ) / (t i : ℚ)) = x

theorem HasRationalDivisorSum.mono_budget {K B C : ℕ} {x : ℚ}
    (h : HasRationalDivisorSum K x B) (hBC : B ≤ C) :
    HasRationalDivisorSum K x C := by
  obtain ⟨k, hk, e, t, het, hsum⟩ := h
  exact ⟨k, hk.trans hBC, e, t, het, hsum⟩

theorem HasRationalDivisorSum.mono_supply {K L B : ℕ} {x : ℚ}
    (h : HasRationalDivisorSum K x B) (hKL : K ∣ L) :
    HasRationalDivisorSum L x B := by
  obtain ⟨k, hk, e, t, het, hsum⟩ := h
  exact ⟨k, hk, e, t, fun i =>
    ⟨(het i).1, (het i).2.1.trans hKL, (het i).2.2⟩, hsum⟩

theorem hasRationalDivisorSum_of_dvd {K s : ℕ} (hs : 0 < s) (hdiv : s ∣ K) :
    HasRationalDivisorSum K (s : ℚ) 1 := by
  refine ⟨1, le_rfl, (fun _ => s), (fun _ => 1), ?_, ?_⟩
  · intro i
    exact ⟨hs, hdiv, by norm_num⟩
  · simp

theorem hasRationalDivisorSum_of_common_denominator {K k t : ℕ} {x : ℚ}
    (e : Fin k → ℕ) (ht : 0 < t) (he : ∀ i, 0 < e i ∧ e i ∣ K)
    (hsum : (∑ i, (e i : ℚ) / (t : ℚ)) = x) :
    HasRationalDivisorSum K x k := by
  exact ⟨k, le_rfl, e, (fun _ => t), fun i => ⟨(he i).1, (he i).2, ht⟩, hsum⟩

theorem HasRationalDivisorSum.add {K B C : ℕ} {x y : ℚ}
    (hx : HasRationalDivisorSum K x B) (hy : HasRationalDivisorSum K y C) :
    HasRationalDivisorSum K (x + y) (B + C) := by
  obtain ⟨k, hk, e, t, het, hsum⟩ := hx
  obtain ⟨l, hl, f, u, hfu, hsum'⟩ := hy
  refine ⟨k + l, Nat.add_le_add hk hl, Fin.append e f, Fin.append t u, ?_, ?_⟩
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa using het j
    · intro j
      simpa using hfu j
  · rw [Fin.sum_univ_add]
    simpa using congrArg₂ (· + ·) hsum hsum'

/-- Three five-term prime representations give fifteen terms. -/
theorem rational_divisor_sum_three {K p q r : ℕ}
    (hp : HasRationalDivisorSum K (p : ℚ) 5)
    (hq : HasRationalDivisorSum K (q : ℚ) 5)
    (hr : HasRationalDivisorSum K (r : ℚ) 5) :
    HasRationalDivisorSum K ((p + q + r : ℕ) : ℚ) 15 := by
  simpa only [Nat.cast_add] using (hp.add hq).add hr

/-- An additional `1/1` fills the parity gap at a cost of one summand. -/
theorem HasRationalDivisorSum.add_one {K B : ℕ} {x : ℚ}
    (h : HasRationalDivisorSum K x B) :
    HasRationalDivisorSum K (x + 1) (B + 1) := by
  simpa using h.add (hasRationalDivisorSum_of_dvd (K := K) (by omega : 0 < 1) (one_dvd K))

/-- Factorial factors absorb every fixed finite exceptional range. -/
theorem rational_divisor_sum_small {K N s : ℕ} (hNK : N.factorial ∣ K)
    (hs : 1 ≤ s) (hsN : s ≤ N) : HasRationalDivisorSum K (s : ℚ) 1 := by
  exact hasRationalDivisorSum_of_dvd hs ((Nat.dvd_factorial hs hsN).trans hNK)

/-- The final arithmetic passage in the rational-divisor supply lemma:
odd integers use fifteen terms, even integers use one more, and a factorial
factor covers the bounded initial interval. -/
theorem rational_divisor_supply_of_odd {K N Y : ℕ} (_hN : 1 ≤ N)
    (hNK : N.factorial ∣ K)
    (hodd : ∀ u : ℕ, N ≤ u → u ≤ Y → Odd u →
      HasRationalDivisorSum K (u : ℚ) 15) :
    ∀ s : ℕ, 1 ≤ s → s ≤ Y → HasRationalDivisorSum K (s : ℚ) 16 := by
  intro s hs hsY
  by_cases hsN : s ≤ N
  · exact (rational_divisor_sum_small hNK hs hsN).mono_budget (by omega)
  · rcases Nat.even_or_odd s with heven | hoddS
    · have hsub : Odd (s - 1) := (Nat.odd_sub' (by omega : 1 ≤ s)).2 (by simpa using heven)
      have hrep := (hodd (s - 1) (by omega) (by omega) hsub).add_one
      have heq : ((s - 1 : ℕ) : ℚ) + 1 = (s : ℚ) := by
        rw [Nat.cast_sub hs, Nat.cast_one]
        ring
      simpa only [heq] using hrep
    · exact (hodd s (by omega) hsY hoddS).mono_budget (by omega)

/-- Package the three-prime combinatorial step without hiding it as an axiom:
any supplied three-summand representations of sufficiently large odd integers
extend, using the factorial fallback, to the complete interval. -/
theorem rational_divisor_supply_of_triples {K N Y : ℕ} (hN : 1 ≤ N)
    (hNK : N.factorial ∣ K)
    (htriples : ∀ u : ℕ, N ≤ u → u ≤ Y → Odd u →
      ∃ p q r : ℕ, p + q + r = u ∧
        HasRationalDivisorSum K (p : ℚ) 5 ∧
        HasRationalDivisorSum K (q : ℚ) 5 ∧
        HasRationalDivisorSum K (r : ℚ) 5) :
    ∀ s : ℕ, 1 ≤ s → s ≤ Y → HasRationalDivisorSum K (s : ℚ) 16 := by
  apply rational_divisor_supply_of_odd hN hNK
  intro u hNu huY huodd
  obtain ⟨p, q, r, hpqr, hp, hq, hr⟩ := htriples u hNu huY huodd
  simpa only [hpqr] using rational_divisor_sum_three hp hq hr

end Problem337

end

end OAI
