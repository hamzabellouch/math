import OAI.Combinatorics.BinaryEdit.FinitePeriod
import OAI.Combinatorics.BinaryEdit.FiniteNumeric

namespace OAI

/-!
# Periods of products supported on few children

This is the period estimate used for sparse active frequencies in
`prop:finite-lower`. An annihilating period suffices; no exact order or lcm
calculation is needed for this step.
-/

open scoped BigOperators

namespace TreeEdit.BinaryLower.FinitePeriod

lemma product_period {ι : Type*} (s : Finset ι) (Q : ℕ)
    (p : ι → ℕ) (z : ι → ℂ)
    (hz : ∀ i ∈ s, z i ^ (Q * p i) = 1) :
    (∏ i ∈ s, z i) ^ (Q * ∏ i ∈ s, p i) = 1 := by
  rw [← Finset.prod_pow]
  apply Finset.prod_eq_one
  intro i hi
  obtain ⟨t, ht⟩ := Nat.mul_dvd_mul_left Q (Finset.dvd_prod_of_mem p hi)
  rw [ht, pow_mul, hz i hi, one_pow]

lemma product_period_pos {ι : Type*} (s : Finset ι) {Q : ℕ}
    (p : ι → ℕ) (hQ : 0 < Q) (hp : ∀ i ∈ s, 0 < p i) :
    0 < Q * ∏ i ∈ s, p i :=
  Nat.mul_pos hQ (Finset.prod_pos hp)

lemma product_period_upper {ι : Type*} (s : Finset ι) {Q k j : ℕ}
    (p : ι → ℕ) (hQ : Q ≤ 2 * k ^ (5 * j))
    (hp : ∀ i ∈ s, p i ≤ k ^ 5) :
    Q * ∏ i ∈ s, p i ≤ 2 * k ^ (5 * j + 5 * s.card) := by
  have hprod : (∏ i ∈ s, p i) ≤ (k ^ 5) ^ s.card := by
    calc
      (∏ i ∈ s, p i) ≤ ∏ _i ∈ s, k ^ 5 :=
        Finset.prod_le_prod hp
      _ = (k ^ 5) ^ s.card := Finset.prod_const _
  calc
    Q * ∏ i ∈ s, p i ≤ (2 * k ^ (5 * j)) * ((k ^ 5) ^ s.card) :=
      Nat.mul_le_mul hQ hprod
    _ = 2 * k ^ (5 * j + 5 * s.card) := by
      rw [← pow_mul, pow_add]
      ring

lemma character_finset_sum {ι A : Type*} [AddCommMonoid A]
    (χ : AddChar A ℂ) (s : Finset ι) (w : ι → A) :
    χ (∑ i ∈ s, w i) = ∏ i ∈ s, χ (w i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [χ.map_zero_eq_one]
  | @insert a s ha ih =>
      simp [ha, χ.map_add_eq_mul, ih]

/-- The product period annihilates the character of the sum, even when the
underlying vectors outside the active set are nonzero. -/
lemma character_supported_period {ι A : Type*} [Fintype ι] [AddCommGroup A]
    (χ : AddChar A ℂ) (s : Finset ι) (w : ι → A) (Q : ℕ) (p : ι → ℕ)
    (houtside : ∀ i, i ∉ s → χ (w i) = 1)
    (hchild : ∀ i ∈ s, (Q * p i) • w i = 0) :
    χ ((Q * ∏ i ∈ s, p i) • ∑ i, w i) = 1 := by
  have hsum : χ (∑ i, w i) = ∏ i ∈ s, χ (w i) := by
    rw [character_finset_sum]
    exact (Finset.prod_subset (Finset.subset_univ s)
      (fun i _ hi => houtside i hi)).symm
  rw [χ.map_nsmul_eq_pow, hsum]
  apply product_period
  intro i hi
  rw [← χ.map_nsmul_eq_pow, hchild i hi, χ.map_zero_eq_one]

/-- Sparse active children are detected by the source's fixed short averaging
interval. All stated inputs are local period and support facts; no Fourier
identity or edit-distance conclusion is assumed here. -/
theorem sparse_character_detection {ι A : Type*} [Fintype ι]
    [AddCommGroup A] [Finite A]
    (χ : AddChar A ℂ) (s : Finset ι) (w : ι → A)
    {k j Q R : ℕ} (p : ι → ℕ)
    (hk : 1 ≤ k) (hj : j < k) (hs : s.card < k)
    (hQpos : 0 < Q) (hQ : Q ≤ 2 * k ^ (5 * j))
    (hppos : ∀ i ∈ s, 0 < p i) (hp : ∀ i ∈ s, p i ≤ k ^ 5)
    (houtside : ∀ i, i ∉ s → χ (w i) = 1)
    (hchild : ∀ i ∈ s, (Q * p i) • w i = 0)
    (hactive : χ (R • ∑ i, w i) ≠ 1) :
    1 ≤ (∑ a ∈ Finset.range (4 * k ^ (10 * k)),
      ‖1 - χ ((a + 1) • ∑ i, w i)‖ ^ 2) / (4 * k ^ (10 * k) : ℕ) := by
  apply character_short_average χ (∑ i, w i)
    (product_period_pos s p hQpos hppos)
    (TreeEdit.BinaryLower.FiniteNumeric.sparse_period_twice_le hk hj hs
      (product_period_upper s p hQ hp)) hactive
  exact character_supported_period χ s w Q p houtside hchild

end TreeEdit.BinaryLower.FinitePeriod

end OAI
