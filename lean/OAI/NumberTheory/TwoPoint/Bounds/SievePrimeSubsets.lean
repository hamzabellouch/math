import OAI.NumberTheory.EgyptianFractions.GoldbachSelbergBound
import OAI.NumberTheory.TwoPoint.Bounds.SieveGoldbachLocal

namespace OAI

/-! Products of prime subsets realize distinct terms of the finite sieve denominator. -/

namespace TwoPointCorrelations

open Finset Problem337
open scoped Classical

lemma sieve_prime_subset_squarefree (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    Squarefree (∏ p ∈ P, p) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    change IsRelPrime p q
    rw [← Nat.coprime_iff_isRelPrime]
    exact (Nat.coprime_primes (hP p hp) (hP q hq)).mpr hpq
  · exact fun p hp => (hP p hp).squarefree

lemma sieve_prime_subset_injective (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    Set.InjOn (fun T : Finset ℕ => ∏ p ∈ T, p) (↑P.powerset : Set (Finset ℕ)) := by
  intro S hS T hT hprod
  have hSp : ∀ p ∈ S, p.Prime := fun p hp => hP p (mem_powerset.mp hS hp)
  have hTp : ∀ p ∈ T, p.Prime := fun p hp => hP p (mem_powerset.mp hT hp)
  calc
    S = (∏ p ∈ S, p).primeFactors := (Nat.primeFactors_prod hSp).symm
    _ = (∏ p ∈ T, p).primeFactors := congrArg Nat.primeFactors hprod
    _ = T := Nat.primeFactors_prod hTp

lemma sieve_prime_subset_weight (N : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    goldbachSieveDensity N (∏ p ∈ P, p) *
      (∏ p ∈ (∏ p ∈ P, p).primeFactors, (1 - goldbachSieveDensity N p)⁻¹) =
      ∏ p ∈ P, sieveGoldbachWeight N p := by
  rw [(goldbachSieveDensity_isMultiplicative N).map_prod_of_prime P hP,
    Nat.primeFactors_prod hP, ← prod_mul_distrib]
  rfl

lemma sieve_prime_subset_log (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    Real.log (∏ p ∈ P, (p : ℝ)) = ∑ p ∈ P, Real.log p := by
  apply Real.log_prod
  intro p hp
  exact_mod_cast (hP p hp).ne_zero

/-- A truncated prime-subset Euler product is a genuine subsum of the actual
Goldbach denominator. -/
theorem sieve_prime_subset_denominator (N z : ℕ) (hN : 2 ∣ N)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    (∑ T ∈ P.powerset with (∏ p ∈ T, p) ≤ z, ∏ p ∈ T, sieveGoldbachWeight N p) ≤
      GoldbachSelberg.denominator N (primorial z) z := by
  let A := P.powerset.filter (fun T => (∏ p ∈ T, p) ≤ z)
  let w := fun d : ℕ => goldbachSieveDensity N d *
    ∏ p ∈ d.primeFactors, (1 - goldbachSieveDensity N p)⁻¹
  have hinj := (sieve_prime_subset_injective P hP).mono (show (↑A : Set (Finset ℕ)) ⊆ ↑P.powerset by
    intro T hT
    exact (mem_filter.mp hT).1)
  have himg : A.image (fun T => ∏ p ∈ T, p) ⊆ (Icc 1 z).filter Squarefree := by
    intro d hd
    obtain ⟨T, hT, rfl⟩ := mem_image.mp hd
    have hTp : ∀ p ∈ T, p.Prime := fun p hp => hP p (mem_powerset.mp (mem_filter.mp hT).1 hp)
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.succ_le_of_lt
      (prod_pos (fun p hp => (hTp p hp).pos)), (mem_filter.mp hT).2⟩,
      sieve_prime_subset_squarefree T hTp⟩
  have hnonneg (d : ℕ) (_hd : d ∈ (Icc 1 z).filter Squarefree) : 0 ≤ w d := by
    have hroot : 0 ≤ goldbachSieveDensity N d := by
      rw [goldbachSieveDensity_apply]
      positivity
    apply mul_nonneg hroot
    apply prod_nonneg
    intro p hp
    exact inv_nonneg.mpr (sub_nonneg.mpr (sieve_goldbach_density_lt_one hN
      (Nat.mem_primeFactors.mp hp).1).le)
  calc
    _ = ∑ T ∈ A, w (∏ p ∈ T, p) := by
      apply sum_congr rfl
      intro T hT
      exact (sieve_prime_subset_weight N T
        (fun p hp => hP p (mem_powerset.mp (mem_filter.mp hT).1 hp))).symm
    _ = ∑ d ∈ A.image (fun T => ∏ p ∈ T, p), w d := (sum_image hinj).symm
    _ ≤ ∑ d ∈ (Icc 1 z).filter Squarefree, w d :=
      sum_le_sum_of_subset_of_nonneg himg (fun d hd _ => hnonneg d hd)
    _ = _ := by rw [GoldbachSelberg.denominator_primorial, sum_filter]

end TwoPointCorrelations

end OAI
