import OAI.NumberTheory.JointDickman.Arithmetic.PrimeMassApproximation
import OAI.NumberTheory.JointDickman.Arithmetic.RoughConvolution

namespace OAI

/-!
# Exact harmonic weights of squarefree prime products

The uncorrected independent-prime mass is the harmonic rough coefficient,
including the empty product. This identifies the weight used in partial summation.
-/

namespace JointDickman

open Finset ArithmeticFunction

theorem primeProduct_squarefree (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    Squarefree (∏ p ∈ S, p) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hS p hp) (hS q hq)).mpr hpq)
  · exact fun p hp => (hS p hp).squarefree

theorem primeProduct_cardFactors (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    cardFactors (∏ p ∈ S, p) = S.card := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hp ih =>
      have hpprime := hS p (mem_insert_self p S)
      have hrest : ∀ q ∈ S, q.Prime := fun q hq => hS q (mem_insert_of_mem hq)
      rw [prod_insert hp, cardFactors_mul hpprime.ne_zero
        (prod_ne_zero_iff.mpr (fun q hq => (hrest q hq).ne_zero)),
        cardFactors_apply_prime hpprime, ih hrest, card_insert_of_notMem hp]
      omega

theorem uncorrectedSubsetMass_harmonic {P S E : Finset ℕ} (z : ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hS : S ⊆ P) (hE : Disjoint S E) :
    uncorrectedSubsetMass P (fun p => z / p) S =
      primeNormalizer P z * roughSquarefreeWeight E z (∏ p ∈ S, p) / (∏ p ∈ S, p : ℕ) := by
  have hSP : ∀ p ∈ S, p.Prime := fun p hp => hP p (hS hp)
  have hrough : roughSquarefreeWeight E z (∏ p ∈ S, p) = z ^ S.card := by
    simp only [roughSquarefreeWeight, ArithmeticFunction.coe_mk, Nat.primeFactors_prod hSP,
      hE, ite_eq_left, squarefreeWeight, primeProduct_squarefree S hSP,
      primeProduct_cardFactors S hSP]
  rw [hrough]
  simp only [uncorrectedSubsetMass, primeNormalizer, prod_div_distrib, prod_const, Nat.cast_prod]
  ring

noncomputable def uncorrectedPrimeProductMass (P : Finset ℕ) (z : ℝ) (n : ℕ) : ℝ :=
  ∑ S ∈ P.powerset, if (∏ p ∈ S, p) = n then
    uncorrectedSubsetMass P (fun p => z / p) S else 0

theorem uncorrectedPrimeProductMass_at_product {P S : Finset ℕ} (z : ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hS : S ⊆ P) :
    uncorrectedPrimeProductMass P z (∏ p ∈ S, p) = uncorrectedSubsetMass P (fun p => z / p) S := by
  classical
  unfold uncorrectedPrimeProductMass
  rw [sum_eq_single S]
  · simp
  · intro T hT hTS
    have hne : (∏ p ∈ T, p) ≠ ∏ p ∈ S, p :=
      fun heq => hTS (primeProduct_injective hP (mem_powerset.mp hT) hS heq)
    simp [hne]
  · intro hn
    exact False.elim (hn (mem_powerset.mpr hS))

theorem uncorrectedPrimeProductMass_eq_zero {P : Finset ℕ} (z : ℝ) (n : ℕ)
    (hn : n ∉ P.powerset.image (fun S => ∏ p ∈ S, p)) :
    uncorrectedPrimeProductMass P z n = 0 := by
  classical
  apply sum_eq_zero
  intro S hS
  have hne : (∏ p ∈ S, p) ≠ n := fun heq => hn (mem_image.mpr ⟨S, hS, heq⟩)
  simp [hne]

theorem uncorrectedPrimeProductMass_harmonic {U : ℝ} {N n : ℕ}
    (hnU : (n : ℝ) ≤ U) (z : ℝ) :
    uncorrectedPrimeProductMass (largePrimeSet U N) z n =
      primeNormalizer (largePrimeSet U N) z * roughSquarefreeWeight (Nat.primesLE N) z n / n := by
  classical
  let P := largePrimeSet U N
  have hP : ∀ p ∈ P, p.Prime := fun p hp => (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2
  by_cases hn : n ∈ P.powerset.image (fun S => ∏ p ∈ S, p)
  · obtain ⟨S, hSP, hSn⟩ := mem_image.mp hn
    have hS : S ⊆ P := mem_powerset.mp hSP
    have hd : Disjoint S (Nat.primesLE N) := by
      apply disjoint_left.mpr
      intro p hp hsmall
      have hgt : (N : ℝ) < p := (mem_filter.mp (hS hp)).2
      have hle : p ≤ N := (Nat.mem_primesLE.mp hsmall).1
      exact (not_lt_of_ge (by exact_mod_cast hle)) hgt
    rw [← hSn, uncorrectedPrimeProductMass_at_product z hP hS]
    exact uncorrectedSubsetMass_harmonic z hP hS hd
  · rw [uncorrectedPrimeProductMass_eq_zero z n hn]
    by_cases hd : Disjoint n.primeFactors (Nat.primesLE N)
    · by_cases hsq : Squarefree n
      · have hsub : n.primeFactors ⊆ P := by
          intro p hp
          have hpprime := Nat.prime_of_mem_primeFactors hp
          have hpn : p ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hsq.ne_zero) (Nat.dvd_of_mem_primeFactors hp)
          have hpU : (p : ℝ) ≤ U := (by exact_mod_cast hpn : (p : ℝ) ≤ n).trans hnU
          have hpN : N < p := by
            by_contra hnot
            exact disjoint_left.mp hd hp (Nat.mem_primesLE.mpr ⟨by omega, hpprime⟩)
          exact mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨Nat.le_floor hpU, hpprime⟩, by exact_mod_cast hpN⟩
        exact False.elim (hn (mem_image.mpr ⟨n.primeFactors, mem_powerset.mpr hsub,
          Nat.prod_primeFactors_of_squarefree hsq⟩))
      · simp [roughSquarefreeWeight, hd, squarefreeWeight, hsq]
    · simp [roughSquarefreeWeight, hd]

open Classical in
theorem primeProductMass_sum_event (P : Finset ℕ) (z : ℝ) (K : Finset ℕ) :
    (∑ n ∈ K, primeProductMass P z n) =
      ∑ S ∈ P.powerset, if (∏ p ∈ S, p) ∈ K then bernoulliSubsetMass P (fun p => z / p) S else 0 := by
  unfold primeProductMass
  rw [sum_comm]
  apply sum_congr rfl
  intro S _
  simp only [eq_comm (a := ∏ p ∈ S, p)]
  simp

open Classical in
theorem uncorrectedPrimeProductMass_sum_event (P : Finset ℕ) (z : ℝ) (K : Finset ℕ) :
    (∑ n ∈ K, uncorrectedPrimeProductMass P z n) =
      ∑ S ∈ P.powerset, if (∏ p ∈ S, p) ∈ K then uncorrectedSubsetMass P (fun p => z / p) S else 0 := by
  unfold uncorrectedPrimeProductMass
  rw [sum_comm]
  apply sum_congr rfl
  intro S _
  simp only [eq_comm (a := ∏ p ∈ S, p)]
  simp

/-- The probability of any bounded set differs from its harmonic rough
weight by at most the reciprocal-square prime tail. -/
theorem primeProductMass_harmonic_error {U : ℝ} {N : ℕ} (hN : N ≠ 0)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) (K : Finset ℕ)
    (hK : ∀ n ∈ K, (n : ℝ) ≤ U) :
    |(∑ n ∈ K, primeProductMass (largePrimeSet U N) z n) -
      primeNormalizer (largePrimeSet U N) z *
        ∑ n ∈ K, roughSquarefreeWeight (Nat.primesLE N) z n / n| ≤ z ^ 2 / (N : ℝ) := by
  have heq : primeNormalizer (largePrimeSet U N) z *
      (∑ n ∈ K, roughSquarefreeWeight (Nat.primesLE N) z n / n) =
      ∑ n ∈ K, uncorrectedPrimeProductMass (largePrimeSet U N) z n := by
    rw [mul_sum]
    apply sum_congr rfl
    intro n hn
    rw [uncorrectedPrimeProductMass_harmonic (hK n hn) z]
    ring
  classical
  have hP : ∀ p ∈ largePrimeSet U (N : ℝ), p.Prime := by
    intro p hp
    exact (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2
  have hcut : ∀ p ∈ largePrimeSet U (N : ℝ), N < p := by
    intro p hp
    exact_mod_cast (mem_filter.mp hp).2
  have h := primeSubsetMass_event_error (largePrimeSet U (N : ℝ)) hP hN hcut hz hz1
    (fun S : Finset ℕ => (∏ p ∈ S, p) ∈ K)
  rw [heq, primeProductMass_sum_event, uncorrectedPrimeProductMass_sum_event]
  convert h using 1
  congr 1
  congr 1 <;> apply sum_congr rfl <;> intro S _ <;> split_ifs <;> rfl

end JointDickman

end OAI
