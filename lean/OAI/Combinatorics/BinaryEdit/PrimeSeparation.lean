import Mathlib

namespace OAI

/-!
# Large-prime divisor counting

The prime-divisor counting estimate gives the arithmetic step in the
finite-tree separation induction, `prop:finite-separation`.
-/

namespace TreeEdit.BinaryLower.PrimeSeparation

open scoped BigOperators

/-- Fewer than `q` distinct primes at least `L` can divide a positive
integer smaller than `L ^ q`. The indexing set need not be all of a type. -/
theorem card_filter_dvd_lt {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ι → ℕ) (L q n : ℕ)
    (hp : ∀ i ∈ s, (p i).Prime)
    (hinj : Set.InjOn p (s : Set ι))
    (hL : ∀ i ∈ s, L ≤ p i)
    (hLpos : 0 < L) (hnpos : 0 < n) (hn : n < L ^ q) :
    (s.filter fun i => p i ∣ n).card < q := by
  classical
  let t := s.filter fun i => p i ∣ n
  have hts : ∀ i ∈ t, i ∈ s := fun i hi => (Finset.mem_filter.mp hi).1
  have hprod : (∏ i ∈ t, p i) ∣ n := by
    apply Finset.prod_dvd_of_isRelPrime
    · intro i hi j hj hij
      apply Nat.coprime_iff_isRelPrime.mp
      apply (Nat.coprime_primes (hp i (hts i hi)) (hp j (hts j hj))).mpr
      exact fun heq => hij (hinj (hts i hi) (hts j hj) heq)
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
  have hprodle : (∏ i ∈ t, p i) ≤ n := Nat.le_of_dvd hnpos hprod
  have hlow : L ^ t.card ≤ ∏ i ∈ t, p i :=
    Finset.pow_card_le_prod t p L fun i hi => hL i (hts i hi)
  change t.card < q
  by_contra h
  have hq : q ≤ t.card := Nat.le_of_not_gt h
  exact (not_le_of_gt hn) ((Nat.pow_le_pow_right hLpos hq).trans (hlow.trans hprodle))

/-- Integer form of `card_filter_dvd_lt`, with no sign restriction. -/
theorem card_filter_int_dvd_lt {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ι → ℕ) (L q : ℕ) (z : ℤ)
    (hp : ∀ i ∈ s, (p i).Prime)
    (hinj : Set.InjOn p (s : Set ι))
    (hL : ∀ i ∈ s, L ≤ p i)
    (hLpos : 0 < L) (hz : z ≠ 0) (hsmall : z.natAbs < L ^ q) :
    (s.filter fun i => (p i : ℤ) ∣ z).card < q := by
  simpa only [Int.natCast_dvd] using
    card_filter_dvd_lt s p L q z.natAbs hp hinj hL hLpos
      (Int.natAbs_pos.mpr hz) hsmall

/-- The numerical divisor estimate used for two different rows of the finite
construction (`T = k^(20*k)`, primes at least `k^4`). -/
theorem finite_tree_few_prime_divisors {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ι → ℕ) (k : ℕ) (z : ℤ)
    (hk : 2 ≤ k) (hp : ∀ i ∈ s, (p i).Prime)
    (hinj : Set.InjOn p (s : Set ι))
    (hlarge : ∀ i ∈ s, k ^ 4 ≤ p i)
    (hz : z ≠ 0) (hsmall : z.natAbs < k ^ (20 * k)) :
    (s.filter fun i => (p i : ℤ) ∣ z).card < 10 * k := by
  apply card_filter_int_dvd_lt s p (k ^ 4) (10 * k) z hp hinj hlarge
  · positivity
  · exact hz
  · apply hsmall.trans_le
    rw [← pow_mul]
    apply Nat.pow_le_pow_right (by omega)
    omega

/-- At least half of the children have periods not dividing the relative
shift between different rows. `Q` is arbitrary here; the product `R` forces
each child prime to divide the distinguished-shift contribution. -/
theorem finite_tree_many_nondividing_children
    (k Q : ℕ) (p : Fin (20 * k) → ℕ) (z t : ℤ)
    (hk : 2 ≤ k) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (hlarge : ∀ i, k ^ 4 ≤ p i)
    (hz : z ≠ 0) (hsmall : z.natAbs < k ^ (20 * k)) :
    10 * k ≤ (Finset.univ.filter fun i =>
      ¬ ((Q * p i : ℕ) : ℤ) ∣ z + t * (∏ j, p j : ℕ)).card := by
  classical
  let R : ℕ := ∏ j, p j
  have hfew : (Finset.univ.filter fun i => (p i : ℤ) ∣ z).card < 10 * k :=
    finite_tree_few_prime_divisors Finset.univ p k z hk (fun i _ => hp i)
      (fun i _ j _ h => hinj h) (fun i _ => hlarge i) hz hsmall
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin (20 * k)))) (fun i => (p i : ℤ) ∣ z)
  have hmany : 10 * k ≤ (Finset.univ.filter fun i => ¬ (p i : ℤ) ∣ z).card := by
    simp only [Finset.card_univ, Fintype.card_fin] at hpartition
    omega
  apply hmany.trans
  apply Finset.card_le_card
  intro i hi
  obtain ⟨_, hnot⟩ := Finset.mem_filter.mp hi
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro hperiod
  have hprimePeriod : (p i : ℤ) ∣ ((Q * p i : ℕ) : ℤ) := by
    refine ⟨(Q : ℤ), ?_⟩
    push_cast
    ring
  have hprimeR : (p i : ℤ) ∣ (R : ℤ) := by
    exact_mod_cast (Finset.dvd_prod_of_mem p (Finset.mem_univ i))
  have hprimeTerm : (p i : ℤ) ∣ t * (R : ℤ) := dvd_mul_of_dvd_right hprimeR t
  have hprimeSum : (p i : ℤ) ∣ z + t * (R : ℤ) := hprimePeriod.trans hperiod
  apply hnot
  simpa only [add_sub_cancel_right] using dvd_sub hprimeSum hprimeTerm

/-- For the same row on both sides, coprimality of the parent period and
`R` prevents every child period from dividing the distinguished shift. -/
theorem not_child_period_dvd_mul (Q R p : ℕ) (t : ℤ)
    (hcop : Nat.Coprime Q R) (ht : ¬ (Q : ℤ) ∣ t) :
    ¬ ((Q * p : ℕ) : ℤ) ∣ t * (R : ℤ) := by
  intro h
  have hparent : (Q : ℤ) ∣ ((Q * p : ℕ) : ℤ) := by
    exact_mod_cast (dvd_mul_right Q p)
  have hn : Q ∣ (t * (R : ℤ)).natAbs := Int.natCast_dvd.mp (hparent.trans h)
  rw [Int.natAbs_mul, Int.natAbs_natCast] at hn
  exact ht (Int.natCast_dvd.mpr (hcop.dvd_mul_right.mp hn))

/-- Complete row-pair arithmetic in Proposition `prop:finite-separation`.
Every pair of legal row indices has at least `m/2 = 10*k` children for which
the relative shift is nonzero modulo the child period. -/
theorem finite_tree_row_pair_nondivisibility
    (k Q : ℕ) (p : Fin (20 * k) → ℕ) (a b : ℕ) (t : ℤ)
    (hk : 2 ≤ k) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (hlarge : ∀ i, k ^ 4 ≤ p i)
    (ha : a < k ^ (20 * k)) (hb : b < k ^ (20 * k))
    (hcop : Nat.Coprime Q (∏ j, p j)) (ht : ¬ (Q : ℤ) ∣ t) :
    10 * k ≤ (Finset.univ.filter fun i =>
      ¬ ((Q * p i : ℕ) : ℤ) ∣
        (b : ℤ) - a + t * (∏ j, p j : ℕ)).card := by
  classical
  by_cases hab : a = b
  · subst b
    simp only [sub_self, zero_add]
    have hall : ∀ i : Fin (20 * k),
        ¬ ((Q * p i : ℕ) : ℤ) ∣ t * (∏ j, p j : ℕ) := fun i =>
      not_child_period_dvd_mul Q (∏ j, p j) (p i) t hcop ht
    simpa only [hall, not_false_eq_true, Finset.filter_true, Finset.card_univ,
      Fintype.card_fin] using (show 10 * k ≤ 20 * k by omega)
  · apply finite_tree_many_nondividing_children k Q p ((b : ℤ) - a) t
      hk hp hinj hlarge
    · omega
    · omega

end TreeEdit.BinaryLower.PrimeSeparation

end OAI
