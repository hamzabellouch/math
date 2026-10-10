import OAI.NumberTheory.JointDickman.Arithmetic.DeletedPrimeFactors
import OAI.NumberTheory.JointDickman.Arithmetic.SieveSingleDensity

namespace OAI

/-! # The Euler product after removing primes dividing j and b -/

namespace JointDickman

open Filter Finset
open scoped Topology

noncomputable def goodSievePrimes (Z j b : ℕ) : Finset ℕ :=
  (sievePrimes Z).filter (fun p => ¬p ∣ j ∧ ¬p ∣ b)

theorem good_sieve_density_bound (κ : ℝ) :
    ∀ᶠ B : ℕ in atTop, ∀ Z j b : ℕ, j ≠ 0 → b ≠ 0 →
      (b : ℝ) ≤ Real.exp (κ * B) → Disjoint b.primeFactors (Nat.primesLE (auxiliaryCutoff B)) →
      (∏ p ∈ goodSievePrimes Z j b, (1 - roughSieveRate (auxiliaryCutoff B) p)) ^ 2 ≤
        roughSieveDensity (auxiliaryCutoff B) Z ^ 2 * singularFactor 24 j * Real.exp 1 := by
  classical
  filter_upwards [large_divisor_inverse_square_bound κ] with B hlarge
  intro Z j b hj hb hbsize hbrough
  let P := sievePrimes Z
  let d := fun p => 1 - roughSieveTheta (auxiliaryCutoff B) p
  let f := fun p => 1 - roughSieveRate (auxiliaryCutoff B) p
  have hP (p : ℕ) (hp : p ∈ P) : p.Prime := (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2
  have hd (p : ℕ) (_hp : p ∈ P) : 0 ≤ d p ∧ d p ≤ 1 := by
    have h := roughSieveTheta_bounds (auxiliaryCutoff B) p
    dsimp [d]
    constructor <;> linarith
  have hf (p : ℕ) (hp : p ∈ P) : 0 < f p ∧ f p ≤ 1 := by
    have h := roughSieveRate_bounds (auxiliaryCutoff B) p (hP p hp)
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
    have hp0 : (0 : ℝ) < p := by linarith
    have hinv : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
    dsimp [f]
    constructor <;> linarith
  have hjfactor : (∏ p ∈ P.filter (fun p => p ∣ j), (f p)⁻¹) ^ 2 ≤ singularFactor 24 j :=
    deleted_divisor_factor_le P hP d hd hj
  let S := P.filter (fun p => p ∣ b)
  have hS : S ⊆ b.primeFactors := fun p hp =>
    (hP p (mem_filter.mp hp).1).mem_primeFactors (mem_filter.mp hp).2 hb
  have hcut (p : ℕ) (hp : p ∈ S) : auxiliaryCutoff B ≤ p := by
    by_contra h
    have hpP : p ∈ Nat.primesLE (auxiliaryCutoff B) :=
      Nat.mem_primesLE.mpr ⟨Nat.le_of_lt (Nat.lt_of_not_ge h), hP p (mem_filter.mp hp).1⟩
    exact disjoint_left.mp hbrough (hS hp) hpP
  have hinv := hlarge b S hb hbsize hS hcut
  have hbprod : (∏ p ∈ S, (f p)⁻¹) ≤ ∏ p ∈ S, (1 - 1 / (p : ℝ))⁻¹ := by
    apply prod_le_prod₀
    · intro p hp
      exact inv_nonneg.mpr (hf p (mem_filter.mp hp).1).1.le
    · intro p hp
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p (mem_filter.mp hp).1).two_le
      have hinvp : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
      apply (inv_le_inv₀ (hf p (mem_filter.mp hp).1).1 (by linarith : 0 < 1 - 1 / (p : ℝ))).mpr
      have h := (roughSieveRate_bounds (auxiliaryCutoff B) p (hP p (mem_filter.mp hp).1)).2.1
      dsimp [f]
      linarith
  have hbfactor : (∏ p ∈ S, (f p)⁻¹) ^ 2 ≤ Real.exp 1 :=
    (pow_le_pow_left₀ (prod_nonneg (fun p hp => inv_nonneg.mpr (hf p (mem_filter.mp hp).1).1.le)) hbprod 2).trans hinv
  have hdelete := delete_two_prime_sets P (fun p => p ∣ j) (fun p => p ∣ b) f hf
  have hpost : (∏ p ∈ P, f p) ^ 2 * (∏ p ∈ P.filter (fun p => p ∣ j), (f p)⁻¹) ^ 2 *
      (∏ p ∈ S, (f p)⁻¹) ^ 2 ≤
      roughSieveDensity (auxiliaryCutoff B) Z ^ 2 * singularFactor 24 j * Real.exp 1 := by
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left hjfactor (sq_nonneg _)
    · exact hbfactor
    · exact sq_nonneg _
    · exact mul_nonneg (sq_nonneg _) (zero_le_one.trans (singularFactor_one_le (by norm_num) j))
  have hdelete' : (∏ p ∈ goodSievePrimes Z j b, f p) ^ 2 ≤
      (∏ p ∈ P, f p) ^ 2 * (∏ p ∈ P.filter (fun p => p ∣ j), (f p)⁻¹) ^ 2 *
        (∏ p ∈ S, (f p)⁻¹) ^ 2 := by
    convert hdelete using 1 <;> simp only [goodSievePrimes, P, S] <;> congr!
  exact hdelete'.trans hpost

end JointDickman

end OAI
