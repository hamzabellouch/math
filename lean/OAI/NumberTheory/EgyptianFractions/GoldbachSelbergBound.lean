import OAI.NumberTheory.EgyptianFractions.OptimizedSelbergError
import OAI.NumberTheory.EgyptianFractions.GoldbachSieveApplication
import OAI.NumberTheory.EgyptianFractions.GoldbachSieveRootBounds

namespace OAI
noncomputable section
open scoped BigOperators
open Finset

namespace Problem337.GoldbachSelberg

/-- The actual multiplicity-preserving sieve for an even target. -/
def sieve (N P : ℕ) (hN : 2 ∣ N) (hP : Squarefree P) : BoundingSieve :=
  PrimePairSieve.imageSieve (Icc 1 (N - 1)) (fun x => x * (N - x)) P hP
    (goldbachSieveDensity N) (goldbachSieveDensity_isMultiplicative N)
    (fun p hp _ => goldbachSieveDensity_prime_pos N p hp)
    (fun p hp _ => goldbachSieveDensity_prime_lt_one N p hp (fun _ => hN))

/-- A concrete finite denominator, independent of proof-valued sieve parameters. -/
def denominator (N P z : ℕ) : ℝ :=
  ∑ d ∈ P.divisors, if d ≤ z then
    goldbachSieveDensity N d *
      ∏ p ∈ d.primeFactors, (1 - goldbachSieveDensity N p)⁻¹ else 0

theorem normalizer_eq_denominator (N P z : ℕ) (hN : 2 ∣ N) (hP : Squarefree P) :
    SelbergOptimal.normalizer (sieve N P hN hP) z = denominator N P z := by
  unfold SelbergOptimal.normalizer denominator
  apply sum_congr rfl
  intro d hd
  rw [BoundingSieve.selbergTerms_apply]
  rfl

theorem denominator_pos (N P : ℕ) (hN : 2 ∣ N) (hP : Squarefree P)
    {z : ℕ} (hz : 1 ≤ z) : 0 < denominator N P z := by
  rw [← normalizer_eq_denominator N P z hN hP]
  exact SelbergOptimal.normalizer_pos _ hz

/-- The local error of this actual sieve is bounded by its actual root count. -/
theorem rem_bound (N P d : ℕ) (hN : 2 ∣ N) (hP : Squarefree P) [NeZero d] :
    |(sieve N P hN hP).rem d| ≤ goldbachSieveRootCount N d := by
  unfold sieve
  rw [PrimePairSieve.imageSieve_rem]
  simpa using goldbach_polynomial_count_density_discrepancy N d

/-- The polynomial root count yields the dimension-two factorizable remainder
bound required by the optimized logarithmic error estimate. -/
theorem rem_lcm_bound (N P : ℕ) (hN : 2 ∣ N) (hP : Squarefree P)
    (a : ℕ) (ha : a ∈ P.divisors) (b : ℕ) (hb : b ∈ P.divisors) :
    |(sieve N P hN hP).rem (Nat.lcm a b)| ≤
      (2 : ℝ) ^ a.primeFactors.card * (2 : ℝ) ^ b.primeFactors.card := by
  let : NeZero a := ⟨(Nat.pos_of_mem_divisors ha).ne'⟩
  let : NeZero b := ⟨(Nat.pos_of_mem_divisors hb).ne'⟩
  let : NeZero (Nat.lcm a b) := ⟨Nat.lcm_ne_zero (NeZero.ne a) (NeZero.ne b)⟩
  have ha2 := goldbachSieveRootCount_le_two_pow N a
    (hP.squarefree_of_dvd (Nat.dvd_of_mem_divisors ha))
  have hb2 := goldbachSieveRootCount_le_two_pow N b
    (hP.squarefree_of_dvd (Nat.dvd_of_mem_divisors hb))
  calc
    _ ≤ (goldbachSieveRootCount N (Nat.lcm a b) : ℝ) := rem_bound N P _ hN hP
    _ ≤ (goldbachSieveRootCount N a : ℝ) * goldbachSieveRootCount N b := by
      exact_mod_cast goldbachSieveRootCount_lcm_le N a b
    _ ≤ _ := by exact_mod_cast Nat.mul_le_mul ha2 hb2

/-- An unconditional, explicit finite upper sieve for ordered Goldbach pairs.
Only evenness, squarefreeness of the chosen sieving product, and `z ≥ 1` are
assumed. The remaining denominator is an actual finite arithmetic sum; no
prime-distribution or unproved remainder estimate is hidden in a premise. -/
theorem primePairs_le (N P : ℕ) (hN : 2 ∣ N) (hP : Squarefree P)
    {z : ℕ} (hz : 1 ≤ z) :
    ((PrimePairSieve.primePairs N).card : ℝ) ≤
      ((N - 1 : ℕ) : ℝ) / denominator N P z +
      (z : ℝ) ^ 2 * (1 + Real.log z) ^ 4 + 2 * P.primeFactors.card := by
  let s := sieve N P hN hP
  have he := SelbergOptimal.siftedSum_le_log_error s hz
    (fun a ha b hb => rem_lcm_bound N P hN hP a ha b hb)
  have hsum : s.siftedSum = ((PrimePairSieve.siftedPairs N P).card : ℝ) :=
    PrimePairSieve.imageSieve_siftedSum _ _ _ _ _ _ _ _
  have hmass : s.totalMass = ((N - 1 : ℕ) : ℝ) := by
    simp [s, sieve, PrimePairSieve.imageSieve]
  have hnorm : SelbergOptimal.normalizer s z = denominator N P z :=
    normalizer_eq_denominator N P z hN hP
  rw [hsum, hmass, hnorm] at he
  have hpairs : ((PrimePairSieve.primePairs N).card : ℝ) ≤
      (PrimePairSieve.siftedPairs N P).card + 2 * P.primeFactors.card := by
    exact_mod_cast PrimePairSieve.card_primePairs_le_sifted N P hP.ne_zero
  linarith

/-- With the primorial cutoff, the denominator is a sum over every squarefree
integer up to the cutoff, not an unspecified subset of them. -/
theorem denominator_primorial (N z : ℕ) :
    denominator N (primorial z) z =
      ∑ d ∈ Icc 1 z, if Squarefree d then
        goldbachSieveDensity N d *
          ∏ p ∈ d.primeFactors, (1 - goldbachSieveDensity N p)⁻¹ else 0 := by
  classical
  unfold denominator
  rw [← sum_filter]
  have hsets : (primorial z).divisors.filter (fun d => d ≤ z) =
      (Icc 1 z).filter Squarefree := by
    ext d
    simp only [mem_filter, mem_Icc]
    constructor
    · rintro ⟨hd, hdz⟩
      exact ⟨⟨Nat.pos_of_mem_divisors hd, hdz⟩,
        (squarefree_primorial z).squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)⟩
    · rintro ⟨⟨hdpos, hdz⟩, hsq⟩
      exact ⟨Nat.mem_divisors.mpr
        ⟨hsq.dvd_primorial.trans (primorial_dvd_primorial hdz),
          primorial_ne_zero z⟩, hdz⟩
  rw [hsets, sum_filter]

/-- The explicit prime-pair sieve at the canonical primorial product. -/
theorem primePairs_le_primorial (N : ℕ) (hN : 2 ∣ N) {z : ℕ} (hz : 1 ≤ z) :
    ((PrimePairSieve.primePairs N).card : ℝ) ≤
      ((N - 1 : ℕ) : ℝ) / denominator N (primorial z) z +
      (z : ℝ) ^ 2 * (1 + Real.log z) ^ 4 + 2 * (Nat.primesLE z).card := by
  simpa only [primeFactors_primorial] using
    primePairs_le N (primorial z) hN (squarefree_primorial z) hz

end Problem337.GoldbachSelberg

end

end OAI
