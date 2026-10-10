import OAI.NumberTheory.EgyptianFractions.FiveProducts
import OAI.NumberTheory.EgyptianFractions.RationalDivisorLift
import OAI.NumberTheory.EgyptianFractions.RationalDivisorSupplyAlgebra
import OAI.NumberTheory.EgyptianFractions.CollisionCounting
import OAI.NumberTheory.EgyptianFractions.PrimeTripleExclusion
import OAI.NumberTheory.EgyptianFractions.SupplyAsymptotics

namespace OAI
noncomputable section
open scoped BigOperators
open Filter
namespace Problem337

/-- The five-product theorem and residue lifting give five rational divisors
for every prime whose divisor-residue image is sufficiently large. -/
theorem rational_divisor_sum_of_large_prime_image (P p : ℕ) (hp : p.Prime)
    (hlarge : (p : ℝ) ^ (3 / 4 : ℝ) <
      (P.divisors.image (fun d : ℕ => (d : ZMod p))).card) :
    HasRationalDivisorSum (P ^ 2) (p : ℚ) 5 := by
  let : Fact p.Prime := ⟨hp⟩
  let H := P.divisors.image (fun d : ℕ => (d : ZMod p))
  obtain ⟨a, b, hsum⟩ := FiveProducts.five_products_zero H hlarge
  obtain ⟨e, t, ht, he, hesum⟩ := rational_divisor_sum_of_residue_products
    (by norm_num : 0 < 5) hp.pos
    (fun i => (a i : ZMod p)) (fun i => (b i : ZMod p))
    (fun i => (a i).property) (fun i => (b i).property) hsum
  exact hasRationalDivisorSum_of_common_denominator e ht he hesum.symm

lemma mod_image_card_eq_zmod_image_card (A : Finset ℕ) (p : ℕ) [NeZero p] :
    (A.image (fun a => a % p)).card =
      (A.image (fun a : ℕ => (a : ZMod p))).card := by
  simpa only [Finset.image_image, Function.comp_def, ZMod.val_natCast] using
    Finset.card_image_of_injective (A.image (fun a : ℕ => (a : ZMod p))) (ZMod.val_injective p)

/-- Ordered prime triples of sum `u`, with their coordinates bounded by `u`. -/
def supplyPrimeTriples (u : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.Icc 1 u) ×ˢ ((Finset.Icc 1 u) ×ˢ (Finset.Icc 1 u))).filter
    (fun t => t.1.Prime ∧ t.2.1.Prime ∧ t.2.2.Prime ∧ t.1 + t.2.1 + t.2.2 = u)

/-- Actual collision counting and the five-product theorem reduce rational
supply for a fixed integer to a lower bound for its number of prime triples. -/
theorem rational_divisor_sum_of_many_prime_triples (u P : ℕ)
    (hu : 2 ≤ u) (hP : 0 < P) (hsize : u ^ 4 ≤ P.divisors.card)
    (htriples : 6 * (u : ℝ) * (u : ℝ) ^ (3 / 4 : ℝ) *
      (Real.log (P : ℝ) / Real.log 2) < (supplyPrimeTriples u).card) :
    HasRationalDivisorSum (P ^ 2) (u : ℚ) 15 := by
  classical
  let U := Finset.Icc 1 u
  let B := U.filter (fun p : ℕ => p.Prime ∧
    ((P.divisors.image (fun a => a % p)).card : ℝ) ≤ (p : ℝ) ^ (3 / 4 : ℝ))
  have hB : (B.card : ℝ) ≤ 2 * (u : ℝ) ^ (3 / 4 : ℝ) *
      (Real.log (P : ℝ) / Real.log 2) := by
    apply exceptional_primes_three_quarters B P.divisors u P hu
    · intro p hp
      obtain ⟨hpU, hprime, _⟩ := Finset.mem_filter.mp hp
      exact ⟨hprime, (Finset.mem_Icc.mp hpU).2⟩
    · intro a ha
      exact ⟨Nat.pos_of_mem_divisors ha, Nat.divisor_le ha⟩
    · omega
    · exact hsize
    · intro p hp
      exact (Finset.mem_filter.mp hp).2.2
  have hUcard : U.card = u := by simp [U, Nat.card_Icc]
  have hsum : ∀ t ∈ supplyPrimeTriples u, t.1 + t.2.1 + t.2.2 = u := by
    intro t ht
    exact (Finset.mem_filter.mp ht).2.2.2.2
  have hU : ∀ t ∈ supplyPrimeTriples u,
      t.1 ∈ U ∧ t.2.1 ∈ U ∧ t.2.2 ∈ U := by
    intro t ht
    exact Finset.mem_product.mp (Finset.mem_filter.mp ht).1 |>.imp_right Finset.mem_product.mp
  have hmany : 3 * B.card * U.card < (supplyPrimeTriples u).card := by
    have hmul := mul_le_mul_of_nonneg_left hB (by positivity : 0 ≤ 3 * (u : ℝ))
    have hbound : (3 : ℝ) * B.card * U.card < (supplyPrimeTriples u).card := by
      rw [hUcard]
      nlinarith [htriples]
    exact_mod_cast hbound
  obtain ⟨t, ht, hpB, hqB, hrB⟩ := exists_fixed_sum_triple_avoiding
    (supplyPrimeTriples u) B U u hsum hU hmany
  have hprime := (Finset.mem_filter.mp ht).2
  have hmem := hU t ht
  have hrepresent (p : ℕ) (hp : p.Prime) (hpU : p ∈ U) (hpB : p ∉ B) :
      HasRationalDivisorSum (P ^ 2) (p : ℚ) 5 := by
    let : NeZero p := ⟨hp.ne_zero⟩
    apply rational_divisor_sum_of_large_prime_image P p hp
    rw [← mod_image_card_eq_zmod_image_card]
    by_contra hn
    apply hpB
    exact Finset.mem_filter.mpr ⟨hpU, hp, le_of_not_gt hn⟩
  have hrep := rational_divisor_sum_three
    (hrepresent t.1 hprime.1 hmem.1 hpB)
    (hrepresent t.2.1 hprime.2.1 hmem.2.1 hqB)
    (hrepresent t.2.2 hprime.2.2.1 hmem.2.2 hrB)
  simpa only [hsum t ht] using hrep

/-- The precise external number-theoretic assertion used by this supply
reduction. It is a proposition, not an axiom or an asserted theorem. -/
def QuantitativeThreePrimeLowerBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ u : ℕ in atTop, Odd u →
    c * ((u : ℝ) ^ 2 / Real.log (u : ℝ) ^ 3) ≤ (supplyPrimeTriples u).card

/-- Once quantitative three-prime input is provided, only elementary growth
properties of the divisor-rich common products are needed for the odd supply. -/
theorem eventually_rational_divisor_sum_of_three_prime_lower_bound
    (P : ℕ → ℕ) (hthree : QuantitativeThreePrimeLowerBound)
    (hP : ∀ᶠ u : ℕ in atTop, 0 < P u ∧ u ^ 4 ≤ (P u).divisors.card)
    (hgrowth : ∃ C : ℝ, ∀ᶠ u : ℕ in atTop,
      Real.log (P u : ℝ) ≤ C * (Real.log (u : ℝ) * Real.log (Real.log (u : ℝ)))) :
    ∀ᶠ u : ℕ in atTop, Odd u →
      HasRationalDivisorSum ((P u) ^ 2) (u : ℚ) 15 := by
  obtain ⟨c, hc, hcount⟩ := hthree
  obtain ⟨C, hgrowth⟩ := hgrowth
  let B : ℕ → ℝ := fun u => 2 * (u : ℝ) ^ (3 / 4 : ℝ) *
    (Real.log (P u : ℝ) / Real.log 2)
  have hB : ∀ᶠ u : ℕ in atTop,
      B u ≤ (2 * C / Real.log 2) *
        ((u : ℝ) ^ (3 / 4 : ℝ) * Real.log (u : ℝ) * Real.log (Real.log (u : ℝ))) := by
    filter_upwards [hgrowth] with u hu
    have hm := mul_le_mul_of_nonneg_left hu
      (show 0 ≤ 2 * (u : ℝ) ^ (3 / 4 : ℝ) / Real.log 2 by positivity)
    dsimp [B]
    calc
      2 * (u : ℝ) ^ (3 / 4 : ℝ) * (Real.log (P u : ℝ) / Real.log 2) =
          (2 * (u : ℝ) ^ (3 / 4 : ℝ) / Real.log 2) * Real.log (P u : ℝ) := by ring
      _ ≤ (2 * (u : ℝ) ^ (3 / 4 : ℝ) / Real.log 2) *
          (C * (Real.log (u : ℝ) * Real.log (Real.log (u : ℝ)))) := hm
      _ = (2 * C / Real.log 2) * ((u : ℝ) ^ (3 / 4 : ℝ) *
          Real.log (u : ℝ) * Real.log (Real.log (u : ℝ))) := by ring
  have hsmall := supply_bad_triples_eventually_lt B (2 * C / Real.log 2) c hc hB
  filter_upwards [hP, hcount, hsmall, eventually_ge_atTop 2] with u hu hcount hsmall hu2
  intro hodd
  apply rational_divisor_sum_of_many_prime_triples u (P u) hu2 hu.1 hu.2
  have hmain := hcount hodd
  have hexception : 6 * (u : ℝ) * (u : ℝ) ^ (3 / 4 : ℝ) *
      (Real.log (P u : ℝ) / Real.log 2) = 3 * (u : ℝ) * B u := by
    dsimp [B]
    ring
  rw [hexception]
  exact hsmall.trans_le hmain

/-- Transfer the eventual odd-integer supply to every integer in the required
initial interval, using nesting and eventual divisibility of each fixed range. -/
theorem eventually_full_rational_supply_of_odd
    (P K : ℕ → ℕ)
    (hodd : ∀ᶠ u : ℕ in atTop, Odd u →
      HasRationalDivisorSum ((P u) ^ 2) (u : ℚ) 15)
    (hnest : ∀ᶠ m : ℕ in atTop, ∀ u : ℕ, 1 ≤ u → u ≤ m ^ 4 → (P u) ^ 2 ∣ K m)
    (hsmall : ∀ N : ℕ, ∀ᶠ m : ℕ in atTop, ∀ s : ℕ, 1 ≤ s → s ≤ N → s ∣ K m) :
    ∀ᶠ m : ℕ in atTop, ∀ s : ℕ, 1 ≤ s → s ≤ m ^ 4 →
      HasRationalDivisorSum (K m) (s : ℚ) 16 := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hodd
  filter_upwards [hnest, hsmall (N + 1)] with m hm hmsmall
  intro s hs hsm
  by_cases hsmallS : s ≤ N + 1
  · exact (hasRationalDivisorSum_of_dvd hs (hmsmall s hs hsmallS)).mono_budget (by omega)
  · rcases Nat.even_or_odd s with hsEven | hsOdd
    · have hsubOdd : Odd (s - 1) :=
        (Nat.odd_sub' hs).2 (by simpa using hsEven)
      have hrep := ((hN (s - 1) (by omega) hsubOdd).mono_supply
        (hm (s - 1) (by omega) (by omega))).add_one
      have heq : ((s - 1 : ℕ) : ℚ) + 1 = (s : ℚ) := by
        rw [Nat.cast_sub hs, Nat.cast_one]
        ring
      simpa only [heq] using hrep
    · exact ((hN s (by omega) hsOdd).mono_supply (hm s hs hsm)).mono_budget (by omega)

/-- Complete conditional supply reduction. Every ingredient other than the
explicit three-prime lower bound is an elementary product-growth interface. -/
theorem eventually_full_rational_supply_of_three_prime_lower_bound
    (P K : ℕ → ℕ) (hthree : QuantitativeThreePrimeLowerBound)
    (hP : ∀ᶠ u : ℕ in atTop, 0 < P u ∧ u ^ 4 ≤ (P u).divisors.card)
    (hgrowth : ∃ C : ℝ, ∀ᶠ u : ℕ in atTop,
      Real.log (P u : ℝ) ≤ C * (Real.log (u : ℝ) * Real.log (Real.log (u : ℝ))))
    (hnest : ∀ᶠ m : ℕ in atTop, ∀ u : ℕ, 1 ≤ u → u ≤ m ^ 4 → (P u) ^ 2 ∣ K m)
    (hsmall : ∀ N : ℕ, ∀ᶠ m : ℕ in atTop, ∀ s : ℕ, 1 ≤ s → s ≤ N → s ∣ K m) :
    ∀ᶠ m : ℕ in atTop, ∀ s : ℕ, 1 ≤ s → s ≤ m ^ 4 →
      HasRationalDivisorSum (K m) (s : ℚ) 16 := by
  exact eventually_full_rational_supply_of_odd P K
    (eventually_rational_divisor_sum_of_three_prime_lower_bound P hthree hP hgrowth)
    hnest hsmall

end Problem337

end

end OAI
