import OAI.Combinatorics.EditDistance.PrimeCharacters

namespace OAI

/-!
# Prime divisibility and distinct phase periods
-/

namespace EditPhase
open scoped BigOperators

lemma few_divisors {J : Type*} [Fintype J] [DecidableEq J]
    (p : J → ℕ) (hp : Pairwise (fun i j => (p i).Coprime (p j)))
    {P r n : ℕ} (hP : 1 ≤ P) (hpP : ∀ j, P ≤ p j)
    (hn : 0 < n) (hnr : n < P ^ r) :
    (Finset.univ.filter (fun j => p j ∣ n)).card < r := by
  let S := Finset.univ.filter (fun j => p j ∣ n)
  have hdiv : (∏ j ∈ S, p j) ∣ n := by
    apply Finset.prod_dvd_of_isRelPrime
    · intro i hi j hj hij
      exact Nat.coprime_iff_isRelPrime.mp (hp hij)
    · intro j hj
      exact (Finset.mem_filter.mp hj).2
  have hlow : P ^ S.card ≤ ∏ j ∈ S, p j :=
    Finset.pow_card_le_prod S p P (fun j _ => hpP j)
  have hle : P ^ S.card ≤ n := hlow.trans (Nat.le_of_dvd hn hdiv)
  by_contra h
  have hcard : r ≤ S.card := Nat.le_of_not_gt h
  have hpow := pow_le_pow_right' hP hcard
  exact (not_lt_of_ge (hpow.trans hle)) hnr

lemma few_prime_divisors {J : Type*} [Fintype J] [DecidableEq J]
    (p : J → ℕ) (hp : ∀ j, (p j).Prime) (hinj : Function.Injective p)
    {P r n : ℕ} (hP : 1 ≤ P) (hpP : ∀ j, P ≤ p j)
    (hn : 0 < n) (hnr : n < P ^ r) :
    (Finset.univ.filter (fun j => p j ∣ n)).card < r := by
  apply few_divisors p (fun i j hij => ?_) hP hpP hn hnr
  exact (Nat.coprime_primes (hp i) (hp j)).mpr (fun h => hij (hinj h))

lemma many_nondivisors_except {J : Type*} [Fintype J] [DecidableEq J]
    (p : J → ℕ) (hp : ∀ j, (p j).Prime) (hinj : Function.Injective p)
    {P r n : ℕ} (hP : 1 ≤ P) (hpP : ∀ j, P ≤ p j)
    (hn : 0 < n) (hnr : n < P ^ r) (i : J) :
    Fintype.card J - r ≤
      (Finset.univ.filter (fun j => j ≠ i ∧ ¬p j ∣ n)).card := by
  have hbad := few_prime_divisors p hp hinj hP hpP hn hnr
  have hsum : (Finset.univ.filter (fun j : J => p j ∣ n)).card +
      (Finset.univ.filter (fun j : J => ¬p j ∣ n)).card = Fintype.card J := by
    exact Finset.card_filter_add_card_filter_not _
  have hins : (Finset.univ.filter (fun j : J => ¬p j ∣ n)) ⊆
      insert i (Finset.univ.filter (fun j => j ≠ i ∧ ¬p j ∣ n)) := by
    intro j hj
    by_cases hji : j = i
    · simp [hji]
    · simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Or.inr ⟨hji, (Finset.mem_filter.mp hj).2⟩
  have hcard := Finset.card_le_card hins
  have hle := Finset.card_insert_le i (Finset.univ.filter (fun j => j ≠ i ∧ ¬p j ∣ n))
  omega

lemma many_nonzero_phases {J : Type*} [Fintype J] [DecidableEq J]
    (p : J → ℕ) (hp : ∀ j, (p j).Prime) (hinj : Function.Injective p)
    {P r : ℕ} (hP : 1 ≤ P) (hpP : ∀ j, P ≤ p j)
    {q : ℤ} (hq : q ≠ 0) (hqr : q.natAbs < P ^ r) (i : J) :
    Fintype.card J - r ≤
      (Finset.univ.filter (fun j => j ≠ i ∧ ¬(p j : ℤ) ∣ q)).card := by
  simpa only [Int.natCast_dvd] using
    many_nondivisors_except p hp hinj hP hpP (Int.natAbs_pos.mpr hq) hqr i

end EditPhase

end OAI
