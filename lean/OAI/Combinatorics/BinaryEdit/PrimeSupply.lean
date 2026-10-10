import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic

namespace OAI

open Filter Finset
open scoped Topology

namespace TreeEdit.BinaryLower.PrimeSupply

/-- The elementary Chebyshev lower bound in the form used by the manuscript. -/
theorem prime_counting_lower :
    ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      c * x / Real.log x ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsmall := Real.isLittleO_log_id_atTop.bound (show 0 < Real.log 2 / 4 by positivity)
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.mp hsmall
  refine ⟨Real.log 2 / 4, by positivity, max 4 a, ?_⟩
  intro x hx
  have hx4 : 4 ≤ x := le_trans (le_max_left _ _) hx
  have hxa : a ≤ x := le_trans (le_max_right _ _) hx
  have hbound := ha (x + 2) (by linarith)
  have hx2 : 0 ≤ x + 2 := by linarith
  simp only [id_eq, Real.norm_eq_abs, abs_of_nonneg hx2] at hbound
  have hlogbound : Real.log (x + 2) ≤ (Real.log 2 / 4) * (x + 2) :=
    (le_abs_self _).trans hbound
  have hxlog : 0 < Real.log x := Real.log_pos (by linarith)
  calc
    (Real.log 2 / 4) * x / Real.log x ≤
        ((x - 1) * Real.log 2 - Real.log (x + 2)) / Real.log x := by
      apply div_le_div_of_nonneg_right _ hxlog.le
      nlinarith
    _ ≤ _ := Chebyshev.pi_ge' (by linarith)

/-- At polynomial arguments, the prime count eventually dominates twice the
preceding power. This is a convenient intermediate form for interval counts. -/
theorem prime_counting_pow_lower (e : ℕ) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      2 * k ^ e ≤ Nat.primeCounting (k ^ (e + 1)) := by
  obtain ⟨c, hc, x₀, hmain⟩ := prime_counting_lower
  have hden : 0 < 2 * ((e + 1 : ℕ) : ℝ) := by positivity
  have hsmall := Real.isLittleO_log_id_atTop.bound (div_pos hc hden)
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.mp hsmall
  obtain ⟨k₀, hk₀⟩ := exists_nat_gt (max 2 (max x₀ a))
  refine ⟨k₀, ?_⟩
  intro k hk
  have hkcast : (k₀ : ℝ) ≤ k := by exact_mod_cast hk
  have hklarge : max 2 (max x₀ a) ≤ (k : ℝ) := le_trans hk₀.le hkcast
  have hk2 : (2 : ℝ) ≤ k := le_trans (le_max_left _ _) hklarge
  have hkx : x₀ ≤ (k : ℝ) :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hklarge
  have hka : a ≤ (k : ℝ) :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hklarge
  have hkzero : (0 : ℝ) ≤ k := by positivity
  have hbound := ha (k : ℝ) hka
  simp only [id_eq, Real.norm_eq_abs, abs_of_nonneg hkzero] at hbound
  have hlogbound : Real.log (k : ℝ) ≤
      c / (2 * ((e + 1 : ℕ) : ℝ)) * k := (le_abs_self _).trans hbound
  have hscaled : Real.log (k : ℝ) * (2 * ((e + 1 : ℕ) : ℝ)) ≤ c * k := by
    apply (le_div_iff₀ hden).mp
    simpa only [div_mul_eq_mul_div] using hlogbound
  have hkpow : (k : ℝ) ≤ (k : ℝ) ^ (e + 1) :=
    le_self_pow₀ (by linarith) (by omega)
  have hcount := hmain ((k : ℝ) ^ (e + 1)) (hkx.trans hkpow)
  have hlogpos : 0 < Real.log ((k : ℝ) ^ (e + 1)) :=
    Real.log_pos (one_lt_pow₀ (by linarith) (by omega))
  have hcompare : 2 * (k : ℝ) ^ e ≤ c * (k : ℝ) ^ (e + 1) /
      Real.log ((k : ℝ) ^ (e + 1)) := by
    apply (le_div_iff₀ hlogpos).mpr
    calc
      2 * (k : ℝ) ^ e * Real.log ((k : ℝ) ^ (e + 1)) =
          (k : ℝ) ^ e * (Real.log (k : ℝ) * (2 * ((e + 1 : ℕ) : ℝ))) := by
        rw [Real.log_pow]
        ring
      _ ≤ (k : ℝ) ^ e * (c * k) :=
        mul_le_mul_of_nonneg_left hscaled (by positivity)
      _ = c * (k : ℝ) ^ (e + 1) := by rw [pow_succ]; ring
  have hreal := hcompare.trans hcount
  norm_cast at hreal
  simpa only [Nat.floor_natCast] using hreal

/-- Removing all integers below `a` from the primes at most `b` loses at most `a`
primes. The inclusive lower endpoint matches the source interval convention. -/
theorem primeCounting_le_interval_card_add (a b : ℕ) :
    Nat.primeCounting b ≤ ((Finset.Icc a b).filter Nat.Prime).card + a := by
  rw [← Nat.primesLE_card_eq_primeCounting]
  have hsub : Nat.primesLE b ⊆ (Finset.Icc a b).filter Nat.Prime ∪ Finset.range a := by
    intro p hp
    obtain ⟨hpb, hprime⟩ := Nat.mem_primesLE.mp hp
    by_cases hpa : a ≤ p
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpa, hpb⟩, hprime⟩)
    · exact Finset.mem_union_right _ (Finset.mem_range.mpr (by omega))
  calc
    (Nat.primesLE b).card ≤ ((Finset.Icc a b).filter Nat.Prime ∪ Finset.range a).card :=
      Finset.card_le_card hsub
    _ ≤ ((Finset.Icc a b).filter Nat.Prime).card + (Finset.range a).card :=
      Finset.card_union_le _ _
    _ = _ := by rw [Finset.card_range]

/-- Consecutive polynomial powers contain at least the lower power in primes,
for all sufficiently large bases. -/
theorem primes_in_power_interval (e : ℕ) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      k ^ e ≤ ((Finset.Icc (k ^ e) (k ^ (e + 1))).filter Nat.Prime).card := by
  obtain ⟨k₀, hk₀⟩ := prime_counting_pow_lower e
  refine ⟨k₀, ?_⟩
  intro k hk
  have hcount := hk₀ k hk
  have hinterval := primeCounting_le_interval_card_add (k ^ e) (k ^ (e + 1))
  omega

/-- Prime supply in the exact two intervals required by the manuscript. -/
theorem prime_supply :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      20 * k ^ 2 ≤ ((Finset.Icc (k ^ 4) (k ^ 5)).filter Nat.Prime).card ∧
      1600 * k < ((Finset.Icc (k ^ 2) (k ^ 3)).filter Nat.Prime).card := by
  obtain ⟨k₄, hk₄⟩ := primes_in_power_interval 4
  obtain ⟨k₂, hk₂⟩ := primes_in_power_interval 2
  refine ⟨max 1601 (max k₄ k₂), ?_⟩
  intro k hk
  have hkbig : 1601 ≤ k := le_trans (le_max_left _ _) hk
  have hk₄' : k₄ ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have hk₂' : k₂ ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk
  constructor
  · have h20 : 20 ≤ k ^ 2 := by nlinarith
    have hmul := Nat.mul_le_mul_right (k ^ 2) h20
    have hlower : 20 * k ^ 2 ≤ k ^ 4 := by nlinarith [hmul]
    exact hlower.trans (hk₄ k hk₄')
  · have hlower : 1600 * k < k ^ 2 := by nlinarith
    exact hlower.trans_le (hk₂ k hk₂')

/-- The globally distinct prime family indexed by depth and child, as used in
`finite-tree.tex`. An embedding makes distinctness over *all* pairs explicit. -/
theorem finite_tree_prime_family :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      ∃ p : (Fin k × Fin (20 * k)) ↪ ℕ,
        ∀ ji, Nat.Prime (p ji) ∧ k ^ 4 ≤ p ji ∧ p ji ≤ k ^ 5 := by
  obtain ⟨k₀, hk₀⟩ := prime_supply
  refine ⟨k₀, ?_⟩
  intro k hk
  have hcard : Fintype.card (Fin k × Fin (20 * k)) ≤
      ((Finset.Icc (k ^ 4) (k ^ 5)).filter Nat.Prime).card := by
    simpa only [Fintype.card_prod, Fintype.card_fin, pow_two, mul_assoc, mul_left_comm] using
      (hk₀ k hk).1
  obtain ⟨p, hp⟩ := Function.Embedding.exists_of_card_le_finset hcard
  refine ⟨p, ?_⟩
  intro ji
  have hmem := hp (Set.mem_range_self ji)
  obtain ⟨hinterval, hprime⟩ := Finset.mem_filter.mp hmem
  exact ⟨hprime, (Finset.mem_Icc.mp hinterval).1, (Finset.mem_Icc.mp hinterval).2⟩

/-- Strengthened finite-tree data: every selected prime is odd (expressed as
strictly greater than two), uniformly over the entire depth/child index set. -/
theorem finite_tree_odd_prime_family :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      2 ≤ k ∧ ∃ p : (Fin k × Fin (20 * k)) ↪ ℕ,
        ∀ ji, Nat.Prime (p ji) ∧ 2 < p ji ∧ k ^ 4 ≤ p ji ∧ p ji ≤ k ^ 5 := by
  obtain ⟨k₀, hk₀⟩ := finite_tree_prime_family
  refine ⟨max 2 k₀, ?_⟩
  intro k hk
  have hk2 : 2 ≤ k := le_trans (le_max_left _ _) hk
  have hkk₀ : k₀ ≤ k := le_trans (le_max_right _ _) hk
  obtain ⟨p, hp⟩ := hk₀ k hkk₀
  refine ⟨hk2, p, ?_⟩
  intro ji
  obtain ⟨hprime, hlow, hupp⟩ := hp ji
  have hpow : 2 ^ 4 ≤ k ^ 4 := Nat.pow_le_pow_left hk2 4
  refine ⟨hprime, ?_, hlow, hupp⟩
  norm_num at hpow
  omega

/-- The torus construction can sample an ordered list of `16*k` distinct
primes, since its prime pool has size strictly greater than `100*(16*k)`. -/
theorem torus_prime_family :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      100 * (16 * k) < ((Finset.Icc (k ^ 2) (k ^ 3)).filter Nat.Prime).card ∧
      ∃ p : Fin (16 * k) ↪ ℕ,
        ∀ i, Nat.Prime (p i) ∧ k ^ 2 ≤ p i ∧ p i ≤ k ^ 3 := by
  obtain ⟨k₀, hk₀⟩ := prime_supply
  refine ⟨k₀, ?_⟩
  intro k hk
  have hlarge := (hk₀ k hk).2
  have hcard : Fintype.card (Fin (16 * k)) ≤
      ((Finset.Icc (k ^ 2) (k ^ 3)).filter Nat.Prime).card := by
    simp only [Fintype.card_fin]
    omega
  obtain ⟨p, hp⟩ := Function.Embedding.exists_of_card_le_finset hcard
  refine ⟨by nlinarith, p, ?_⟩
  intro i
  have hmem := hp (Set.mem_range_self i)
  obtain ⟨hinterval, hprime⟩ := Finset.mem_filter.mp hmem
  exact ⟨hprime, (Finset.mem_Icc.mp hinterval).1, (Finset.mem_Icc.mp hinterval).2⟩

end TreeEdit.BinaryLower.PrimeSupply

end OAI
