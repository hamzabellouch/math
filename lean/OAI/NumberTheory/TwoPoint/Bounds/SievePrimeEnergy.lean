import OAI.NumberTheory.TwoPoint.Bounds.SieveUniformPairs
import OAI.NumberTheory.TwoPoint.Bounds.SieveSingularAverage
import Mathlib.Combinatorics.Additive.Energy

namespace OAI

/-! Prime additive energy from the finite Goldbach sieve and the singular-factor mean square. -/

namespace TwoPointCorrelations

open Finset Filter Problem337
open scoped Classical Pointwise

lemma sieve_prime_pair_card (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (N : ℕ) :
    ((P ×ˢ P).filter (fun v => v.1 + v.2 = N)).card ≤ (PrimePairSieve.primePairs N).card := by
  apply card_le_card_of_injOn Prod.fst
  · rintro ⟨p, q⟩ hpq
    obtain ⟨hpq, hsum⟩ := mem_filter.mp hpq
    obtain ⟨hp, hq⟩ := mem_product.mp hpq
    have hp2 := (hP p hp).two_le
    have hq2 := (hP q hq).two_le
    apply mem_filter.mpr
    exact ⟨mem_Icc.mpr ⟨by omega, by omega⟩,
      hP p hp, by convert hP q hq using 1; omega⟩
  · rintro ⟨p, q⟩ hpq ⟨r, s⟩ hrs heq
    have hsum1 := (mem_filter.mp hpq).2
    have hsum2 := (mem_filter.mp hrs).2
    change p = r at heq
    apply Prod.ext heq
    omega

lemma sieve_prime_sum_even {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    {N : ℕ} (hN : N ∈ P + P) : 2 ∣ N := by
  obtain ⟨p, hp, q, hq, rfl⟩ := mem_add.mp hN
  have hpodd := (hP p hp).1.odd_of_ne_two (hP p hp).2
  have hqodd := (hP q hq).1.odd_of_ne_two (hP q hq).2
  exact (hpodd.add_odd hqodd).two_dvd

/-- The number of zero-sum prime quadruples has the required four logarithms
uniformly for every finite prime set below twice the scale. -/
theorem sieve_prime_additive_energy :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop, ∀ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ p ≠ 2 ∧ (p : ℝ) ≤ 2 * x) →
      (Finset.addEnergy P P : ℝ) ≤ C * x ^ 3 / Real.log x ^ 4 := by
  obtain ⟨C, hC, hevent⟩ := sieve_goldbach_pairs_uniform
  refine ⟨4 * C ^ 2 * (sieveSingularMeanConstant + 1), by
    have := sieve_singular_mean_constant_nonneg
    positivity, ?_⟩
  filter_upwards [hevent] with x hx
  obtain ⟨hx1, hxlog, hpairs⟩ := hx
  intro P hP
  have hx0 : 0 < x := by linarith
  have hlog0 : 0 < Real.log x := by linarith
  let A := C * x / Real.log x ^ 2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hsub : P + P ⊆ Icc 1 ⌊4 * x⌋₊ := by
    intro N hN
    obtain ⟨p, hp, q, hq, rfl⟩ := mem_add.mp hN
    have hp2 := (hP p hp).1.two_le
    have hq2 := (hP q hq).1.two_le
    apply mem_Icc.mpr
    constructor
    · omega
    · apply (Nat.le_floor_iff (by positivity : 0 ≤ 4 * x)).mpr
      push_cast
      linarith [(hP p hp).2.2, (hP q hq).2.2]
  have hpair (N : ℕ) (hN : N ∈ P + P) :
      (((P ×ˢ P).filter (fun v => v.1 + v.2 = N)).card : ℝ) ≤ A * sieveSingularFactor N := by
    have hNI := mem_Icc.mp (hsub hN)
    have hNx : (N : ℝ) ≤ 4 * x :=
      (show (N : ℝ) ≤ ⌊4 * x⌋₊ by exact_mod_cast hNI.2).trans (Nat.floor_le (by positivity))
    calc
      _ ≤ ((PrimePairSieve.primePairs N).card : ℝ) := by
        exact_mod_cast sieve_prime_pair_card P (fun p hp => (hP p hp).1) N
      _ ≤ C * x * sieveSingularFactor N / Real.log x ^ 2 := hpairs N (by omega)
        (sieve_prime_sum_even (fun p hp => ⟨(hP p hp).1, (hP p hp).2.1⟩) hN) hNx
      _ = _ := by dsimp [A]; ring
  have henergy : (Finset.addEnergy P P : ℝ) ≤
      A ^ 2 * (∑ N ∈ Icc 1 ⌊4 * x⌋₊, sieveSingularFactor N ^ 2) := by
    rw [Finset.addEnergy_eq_sum_sq', Nat.cast_sum]
    calc
      _ = ∑ N ∈ P + P, (((P ×ˢ P).filter (fun v => v.1 + v.2 = N)).card : ℝ) ^ 2 := by
        simp only [Nat.cast_pow]
      _ ≤ ∑ N ∈ P + P, (A * sieveSingularFactor N) ^ 2 := by
        apply sum_le_sum
        intro N hN
        exact pow_le_pow_left₀ (Nat.cast_nonneg _) (hpair N hN) 2
      _ = A ^ 2 * (∑ N ∈ P + P, sieveSingularFactor N ^ 2) := by
        simp only [mul_pow, mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (sum_le_sum_of_subset_of_nonneg hsub (fun N _ _ => sq_nonneg _)) (sq_nonneg _)
  have havg := sieve_singular_square_average ⌊4 * x⌋₊
  have hfloor := Nat.floor_le (by positivity : 0 ≤ 4 * x)
  have hK := sieve_singular_mean_constant_nonneg
  calc
    _ ≤ A ^ 2 * (sieveSingularMeanConstant * ⌊4 * x⌋₊) :=
      henergy.trans (mul_le_mul_of_nonneg_left havg (sq_nonneg _))
    _ ≤ A ^ 2 * (sieveSingularMeanConstant * (4 * x)) := by
      gcongr
    _ ≤ A ^ 2 * ((sieveSingularMeanConstant + 1) * (4 * x)) := by
      gcongr
      linarith
    _ = _ := by dsimp [A]; ring

end TwoPointCorrelations

end OAI
