import OAI.NumberTheory.EgyptianFractions.CompositeRationalSupply
import OAI.NumberTheory.EgyptianFractions.DenseModularSupply

namespace OAI
noncomputable section

namespace Problem337

/-- Removing the full common prime-power part leaves a coprime quotient.
Only primes of the supply need the displayed multiplicity bound. -/
theorem coprime_div_gcd_pow_of_prime_power_free {q P r : ℕ}
    (hq : 0 < q) (hP : 0 < P)
    (hfree : ∀ p : ℕ, p.Prime → p ∣ P → ¬p ^ (r + 1) ∣ q) :
    Nat.Coprime (q / Nat.gcd q (P ^ r)) P := by
  have hg := Nat.gcd_dvd_left q (P ^ r)
  have hgpos : 0 < Nat.gcd q (P ^ r) := Nat.pos_of_dvd_of_pos hg hq
  have hquot : q / Nat.gcd q (P ^ r) ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd hq hg) hgpos).ne'
  apply Nat.coprime_of_dvd
  intro p hp hpd hpP
  have hsmall : q.factorization p ≤ r := by
    have hh := hfree p hp hpP
    rw [hp.pow_dvd_iff_le_factorization hq.ne'] at hh
    omega
  have hPlarge : 1 ≤ P.factorization p :=
    (hp.dvd_iff_one_le_factorization hP.ne').mp hpP
  have hle : q.factorization p ≤ r * P.factorization p :=
    hsmall.trans (by nlinarith)
  have hpos := hp.factorization_pos_of_dvd hquot hpd
  rw [Nat.factorization_div hg,
    Nat.factorization_gcd hq.ne' (pow_ne_zero _ hP.ne'), Nat.factorization_pow] at hpos
  simp [Finsupp.coe_tsub, Finsupp.inf_apply, Finsupp.smul_apply,
    smul_eq_mul, min_eq_left hle] at hpos

/-- The finite cube-free splitting used by composite-modulus supply. No
squarefreeness of `P` is needed; repeated primes only make the removal larger. -/
theorem cube_free_supply_split {q P : ℕ} (hq : 0 < q) (hP : 0 < P)
    (hfree : ∀ p : ℕ, p.Prime → ¬p ^ 3 ∣ q) :
    ∃ g d : ℕ, 0 < g ∧ 0 < d ∧ g ∣ P ^ 2 ∧
      d ∣ q ∧ g * d = q ∧ Nat.Coprime d P := by
  let g := Nat.gcd q (P ^ 2)
  have hgq : g ∣ q := Nat.gcd_dvd_left _ _
  have hg : 0 < g := Nat.pos_of_dvd_of_pos hgq hq
  refine ⟨g, q / g, hg, Nat.div_pos (Nat.le_of_dvd hq hgq) hg,
    Nat.gcd_dvd_right _ _, Nat.div_dvd_of_dvd hgq, ?_, ?_⟩
  · exact Nat.mul_div_cancel' hgq
  · exact coprime_div_gcd_pow_of_prime_power_free hq hP
      (fun p hp _ => by simpa using hfree p hp)

/-- A representation of the coprime quotient, whose numerators divide `P²`,
rescales to the original integer with numerators dividing `P⁴`, and no increase
in the number of summands. -/
theorem rational_divisor_sum_of_gcd_square_quotient {q P B : ℕ}
    (hq : 0 < q)
    (hrep : HasRationalDivisorSum (P ^ 2) ((q / Nat.gcd q (P ^ 2) : ℕ) : ℚ) B) :
    HasRationalDivisorSum (P ^ 4) (q : ℚ) B := by
  have hgq := Nat.gcd_dvd_left q (P ^ 2)
  have hgpos : 0 < Nat.gcd q (P ^ 2) := Nat.pos_of_dvd_of_pos hgq hq
  have hg := hasRationalDivisorSum_of_dvd hgpos (Nat.gcd_dvd_right q (P ^ 2))
  have h := hg.mul hrep
  have heq : P ^ 2 * P ^ 2 = P ^ 4 := by ring
  have hqeq : Nat.gcd q (P ^ 2) * (q / Nat.gcd q (P ^ 2)) = q :=
    Nat.mul_div_cancel' hgq
  simpa only [heq, one_mul, ← Nat.cast_mul, hqeq] using h

/-- Supplying the coprime divisors is enough to supply a cube-free integer.
The coprime-divisor premise includes `1`, so no exceptional zero-frequency
or unit-modulus case is being suppressed. -/
theorem rational_divisor_sum_of_cube_free_divisor_supply {q P B : ℕ}
    (hq : 0 < q) (hP : 0 < P)
    (hfree : ∀ p : ℕ, p.Prime → ¬p ^ 3 ∣ q)
    (hrep : ∀ d : ℕ, 0 < d → d ∣ q → Nat.Coprime d P →
      HasRationalDivisorSum (P ^ 2) (d : ℚ) B) :
    HasRationalDivisorSum (P ^ 4) (q : ℚ) B := by
  apply rational_divisor_sum_of_gcd_square_quotient hq
  have hg := Nat.gcd_dvd_left q (P ^ 2)
  apply hrep
  · exact Nat.div_pos (Nat.le_of_dvd hq hg) (Nat.pos_of_dvd_of_pos hg hq)
  · exact Nat.div_dvd_of_dvd hg
  · exact coprime_div_gcd_pow_of_prime_power_free hq hP
      (fun p hp _ => by simpa using hfree p hp)

/-- Finite assembly for the canonical marked-grouping interface. The unknown
arithmetic inputs remain explicit: density of good cube-free moduli, and
bounded rational-divisor supply for their coprime divisors. -/
theorem marked_rational_supply_of_cube_free_set
    (m P B : ℕ) (G : Finset ℕ) (hP : 0 < P)
    (hG : G ⊆ Finset.Icc 1 (m ^ 4))
    (hcard : 2 * m ^ 4 < 3 * G.card)
    (hfree : ∀ q ∈ G, ∀ p : ℕ, p.Prime → ¬p ^ 3 ∣ q)
    (hrep : ∀ q ∈ G, ∀ d : ℕ, 0 < d → d ∣ q → Nat.Coprime d P →
      HasRationalDivisorSum (P ^ 2) (d : ℚ) B) :
    HasRationalDivisorSupply m (P ^ 4) (2 * B) := by
  apply rational_divisor_supply_bridge
  apply rational_divisor_supply_of_two_thirds (P ^ 4) B (m ^ 4) G hG hcard
  intro q hq
  exact rational_divisor_sum_of_cube_free_divisor_supply
    (Finset.mem_Icc.mp (hG hq)).1 hP (hfree q hq) (hrep q hq)

end Problem337

end

end OAI
