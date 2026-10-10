import OAI.Combinatorics.LowSpaceSubsetSum.Counting.PrimeHashCollision

namespace OAI

/-!
# Overflow probability for one fixed solution bucket

Equal actual weights are separated before prime collision estimates. A finite
set of weight--mask keys may contain many keys with the same weight; linearity
of expectation counts every such key when its weight differs from the fixed
solution's weight. This is the bucket argument in both trial analyses.
-/

namespace LowSpaceSubsetSum

open scoped BigOperators

variable {Ω α β : Type*} [DecidableEq β]

def sameWeightKeys (X : Finset α) (value : α → ℤ) (x : α) : Finset α :=
  X.filter fun y => value y = value x

def otherCollisionKeys (X : Finset α) (value : α → ℤ) (hash : ℤ → β)
    (x : α) : Finset α :=
  (X.filter fun y => value y ≠ value x).filter fun y => hash (value y) = hash (value x)

def hashBucket (X : Finset α) (value : α → ℤ) (hash : ℤ → β) (x : α) : Finset α :=
  X.filter fun y => hash (value y) = hash (value x)

theorem hashBucket_card (X : Finset α) (value : α → ℤ) (hash : ℤ → β) (x : α) :
    (hashBucket X value hash x).card =
      (sameWeightKeys X value x).card + (otherCollisionKeys X value hash x).card := by
  classical
  have heq : hashBucket X value hash x =
      sameWeightKeys X value x ∪ otherCollisionKeys X value hash x := by
    ext y
    by_cases h : value y = value x <;>
      simp [hashBucket, sameWeightKeys, otherCollisionKeys, h]
  rw [heq, Finset.card_union_of_disjoint]
  apply Finset.disjoint_left.mpr
  intro y hy hz
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).2 (Finset.mem_filter.mp hy).2

theorem expected_otherCollisionKeys_le (seeds : Finset Ω) (prob : Ω → ℝ)
    (X : Finset α) (value : α → ℤ) (hash : Ω → ℤ → β) {x : α} (hx : x ∈ X)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hcollision : PairwiseCollisionBound seeds prob (X.image value) hash δ) :
    (∑ ω ∈ seeds, prob ω * (otherCollisionKeys X value (hash ω) x).card) ≤
      δ * X.card := by
  classical
  let others := X.filter fun y => value y ≠ value x
  have hcard (ω : Ω) : ((otherCollisionKeys X value (hash ω) x).card : ℝ) =
      ∑ y ∈ others, if hash ω (value y) = hash ω (value x) then (1 : ℝ) else 0 := by
    simp [others, otherCollisionKeys]
  simp_rw [hcard, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ _y ∈ others, δ := by
      apply Finset.sum_le_sum
      intro y hy
      obtain ⟨hyX, hyne⟩ := Finset.mem_filter.mp hy
      exact hcollision (value y) (Finset.mem_image.mpr ⟨y, hyX, rfl⟩)
        (value x) (Finset.mem_image.mpr ⟨x, hx, rfl⟩) hyne
    _ ≤ δ * X.card := by
      have hcard : (others.card : ℝ) ≤ X.card := by
        exact_mod_cast Finset.card_filter_le (s := X) (p := fun y => value y ≠ value x)
      simpa only [Finset.sum_const, nsmul_eq_mul, mul_comm] using
        mul_le_mul_of_nonneg_left hcard hδ

/-- Weighted finite Markov for any nonnegative counted quantity. -/
theorem probability_count_le (seeds : Finset Ω) (prob : Ω → ℝ) (count : Ω → ℕ)
    (hnonneg : ∀ ω ∈ seeds, 0 ≤ prob ω) (hprob : ∑ ω ∈ seeds, prob ω = 1)
    {M T : ℝ} (hT : 0 < T)
    (hmean : (∑ ω ∈ seeds, prob ω * count ω) ≤ M) :
    1 - M / T ≤ ∑ ω ∈ seeds.filter (fun ω => (count ω : ℝ) ≤ T), prob ω := by
  classical
  let bad := seeds.filter fun ω => T < (count ω : ℝ)
  have hbad : T * (∑ ω ∈ bad, prob ω) ≤ M := by
    calc
      _ = ∑ ω ∈ bad, prob ω * T := by rw [Finset.mul_sum]; simp [mul_comm]
      _ ≤ ∑ ω ∈ bad, prob ω * count ω := by
        apply Finset.sum_le_sum
        intro ω hω
        have hm := Finset.mem_filter.mp hω
        exact mul_le_mul_of_nonneg_left hm.2.le (hnonneg ω hm.1)
      _ ≤ ∑ ω ∈ seeds, prob ω * count ω := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro ω hω _
        exact mul_nonneg (hnonneg ω hω) (Nat.cast_nonneg _)
      _ ≤ M := hmean
  have hbad' : (∑ ω ∈ bad, prob ω) ≤ M / T := by
    apply (le_div_iff₀ hT).mpr
    simpa only [mul_comm] using hbad
  have hpart : (∑ ω ∈ seeds.filter (fun ω => (count ω : ℝ) ≤ T), prob ω) +
      (∑ ω ∈ bad, prob ω) = 1 := by
    simp only [bad, Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    convert hprob using 1
    apply Finset.sum_congr rfl
    intro ω _
    by_cases hω : (count ω : ℝ) ≤ T
    · simp [hω, not_lt_of_ge hω]
    · simp [hω, lt_of_not_ge hω]
  linarith

theorem fixed_bucket_fits_probability (seeds : Finset Ω) (prob : Ω → ℝ)
    (X : Finset α) (value : α → ℤ) (hash : Ω → ℤ → β) {x : α} (hx : x ∈ X)
    (hnonneg : ∀ ω ∈ seeds, 0 ≤ prob ω) (hprob : ∑ ω ∈ seeds, prob ω = 1)
    {C : ℕ} (hC : 0 < C) (hequal : ((sameWeightKeys X value x).card : ℝ) ≤ (C : ℝ) / 2)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hcollision : PairwiseCollisionBound seeds prob (X.image value) hash δ) :
    1 - 2 * δ * X.card / C ≤
      ∑ ω ∈ seeds.filter (fun ω => (hashBucket X value (hash ω) x).card ≤ C), prob ω := by
  classical
  have hCR : (0 : ℝ) < C := by exact_mod_cast hC
  have hmean := expected_otherCollisionKeys_le seeds prob X value hash hx hδ hcollision
  have hmarkov := probability_count_le seeds prob
    (fun ω => (otherCollisionKeys X value (hash ω) x).card) hnonneg hprob
    (by positivity : (0 : ℝ) < (C : ℝ) / 2) hmean
  have hrewrite : (δ * X.card) / ((C : ℝ) / 2) = 2 * δ * X.card / C := by ring
  rw [hrewrite] at hmarkov
  apply hmarkov.trans
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro ω hω
    obtain ⟨hmem, hother⟩ := Finset.mem_filter.mp hω
    apply Finset.mem_filter.mpr
    refine ⟨hmem, ?_⟩
    rw [hashBucket_card]
    have hsum : ((sameWeightKeys X value x).card : ℝ) +
        (otherCollisionKeys X value (hash ω) x).card ≤ C := by linarith
    exact_mod_cast hsum
  · intro ω hω _
    exact hnonneg ω (Finset.mem_filter.mp hω).1

/-- Concrete extra-prime bucket success. The equal-weight capacity premise
is supplied separately by the mask-counting lemmas in `Buckets`. -/
theorem prime_fixed_bucket_fits_probability (X : Finset α) (value : α → ℤ)
    {x : α} (hx : x ∈ X) {ell u C : ℕ} (hell : 4 ≤ ell) (hellu : ell ≤ u)
    (hC : 0 < C) (hequal : ((sameWeightKeys X value x).card : ℝ) ≤ (C : ℝ) / 2)
    (hbits : ∀ y ∈ X, ∀ z ∈ X, (value y - value z).natAbs < 2 ^ (2 * u)) :
    1 - 16 * (u : ℝ) ^ 2 * X.card / ((C : ℝ) * (2 : ℝ) ^ ell) ≤
      ∑ p ∈ (primeRange ell).filter
        (fun (p : ℕ) => (hashBucket X value (fun w => w % (p : ℤ)) x).card ≤ C),
          primeProbability ell p := by
  have hcollision := prime_pairwise_collision_bound (X.image value) hell hellu (by
    intro y hy z hz
    obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨z', hz', rfl⟩ := Finset.mem_image.mp hz
    exact hbits y' hy' z' hz')
  have h := fixed_bucket_fits_probability (primeRange ell) (primeProbability ell)
    X value (fun (p : ℕ) w => w % (p : ℤ)) hx
    (by intro p _; exact div_nonneg zero_le_one (Nat.cast_nonneg _))
    (primeProbability_sum hell) hC hequal
    (δ := 8 * (u : ℝ) ^ 2 / (2 : ℝ) ^ ell) (by positivity) hcollision
  convert h using 1
  ring

end LowSpaceSubsetSum

end OAI
