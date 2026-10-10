import Mathlib

namespace OAI
noncomputable section

open scoped BigOperators

namespace Problem337

/-- Nonzero residue classes modulo `p`. For prime `p`, these are exactly
its unit classes. -/
def threePrimeNonzeroResidues (p : ℕ) [NeZero p] : Finset (ZMod p) :=
  Finset.univ.erase 0

/-- Two-coordinate parametrization of nonzero residue triples with sum `u`:
the third coordinate is `u - x - y`. -/
def threePrimeLocalPairs (p : ℕ) [NeZero p] (u : ZMod p) :
    Finset (ZMod p × ZMod p) :=
  (threePrimeNonzeroResidues p ×ˢ threePrimeNonzeroResidues p).filter
    (fun t => t.1 + t.2 ≠ u)

lemma mem_threePrimeLocalPairs {p : ℕ} [NeZero p]
    (u x y : ZMod p) :
    (x, y) ∈ threePrimeLocalPairs p u ↔
      x ≠ 0 ∧ y ≠ 0 ∧ u - x - y ≠ 0 := by
  simp only [threePrimeLocalPairs, threePrimeNonzeroResidues,
    Finset.mem_filter, Finset.mem_product, Finset.mem_erase,
    Finset.mem_univ, and_true]
  constructor
  · rintro ⟨⟨hx, hy⟩, hsum⟩
    refine ⟨hx, hy, ?_⟩
    intro hz
    apply hsum
    linear_combination -hz
  · rintro ⟨hx, hy, hz⟩
    refine ⟨⟨hx, hy⟩, ?_⟩
    intro hsum
    apply hz
    linear_combination -hsum

lemma threePrimeLocalBadPairs_eq_image {p : ℕ} [NeZero p] (u : ZMod p) :
    (threePrimeNonzeroResidues p ×ˢ threePrimeNonzeroResidues p).filter
        (fun t => t.1 + t.2 = u) =
      ((threePrimeNonzeroResidues p).erase u).image (fun x => (x, u - x)) := by
  classical
  ext t
  rcases t with ⟨x, y⟩
  simp only [threePrimeNonzeroResidues, Finset.mem_filter, Finset.mem_product,
    Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨hx, hy⟩, hsum⟩
    refine ⟨x, ⟨?_, hx⟩, rfl, ?_⟩
    · intro hxu
      apply hy
      linear_combination hsum - hxu
    · linear_combination -hsum
  · rintro ⟨a, ⟨hau, ha⟩, hax, hay⟩
    subst a
    refine ⟨⟨ha, ?_⟩, ?_⟩
    · intro hy
      apply hau
      linear_combination -hay - hy
    · linear_combination -hay

lemma threePrimeNonzeroResidues_card (p : ℕ) [NeZero p] :
    (threePrimeNonzeroResidues p).card = p - 1 := by
  simp [threePrimeNonzeroResidues]

/-- Removing the forbidden third-coordinate-zero pairs leaves this exact
cardinality balance. This identity uses only the additive residue group. -/
theorem threePrimeLocalPairs_card_balance (p : ℕ) [NeZero p] (u : ZMod p) :
    (threePrimeLocalPairs p u).card +
      ((threePrimeNonzeroResidues p).erase u).card = (p - 1) ^ 2 := by
  classical
  have hcard := Finset.card_filter_add_card_filter_not
    (s := threePrimeNonzeroResidues p ×ˢ threePrimeNonzeroResidues p)
    (p := fun t : ZMod p × ZMod p => t.1 + t.2 = u)
  rw [threePrimeLocalBadPairs_eq_image] at hcard
  have hinj : Function.Injective (fun x : ZMod p => (x, u - x)) := by
    intro x y hxy
    exact congrArg Prod.fst hxy
  rw [Finset.card_image_of_injective _ hinj] at hcard
  simpa [threePrimeLocalPairs, Finset.card_product,
    threePrimeNonzeroResidues_card, pow_two, add_comm] using hcard

/-- Exact count of the local nonzero solutions to a three-term sum. -/
theorem threePrimeLocalPairs_card (p : ℕ) [NeZero p] (hp : 2 ≤ p)
    (u : ZMod p) :
    (threePrimeLocalPairs p u).card =
      if u = 0 then (p - 1) * (p - 2) else (p - 1) * (p - 2) + 1 := by
  classical
  have hbalance := threePrimeLocalPairs_card_balance p u
  have hdiff : p - 1 = (p - 2) + 1 := by omega
  by_cases hu : u = 0
  · subst u
    simp [threePrimeNonzeroResidues] at hbalance
    simp only [ite_true, eq_self]
    rw [hdiff] at hbalance ⊢
    nlinarith
  · have hmem : u ∈ threePrimeNonzeroResidues p := by
      simp [threePrimeNonzeroResidues, hu]
    rw [Finset.card_erase_of_mem hmem, threePrimeNonzeroResidues_card] at hbalance
    simp only [ite_eq_right hu]
    rw [hdiff] at hbalance ⊢
    simp only [Nat.add_sub_cancel] at hbalance
    nlinarith

/-- Polynomial form of the local solution count. -/
theorem threePrimeLocalPairs_card_real (p : ℕ) [NeZero p] (hp : 2 ≤ p)
    (u : ZMod p) :
    ((threePrimeLocalPairs p u).card : ℝ) =
      (p : ℝ) ^ 2 - 3 * p + 3 - if u = 0 then 1 else 0 := by
  rw [threePrimeLocalPairs_card p hp u]
  split_ifs <;> push_cast [Nat.cast_sub (show 1 ≤ p by omega), Nat.cast_sub hp] <;> ring

/-- The local density relative to the heuristic density of three unit classes.
The prime hypothesis is used when identifying this with a singular-series
factor; the finite expression is defined for every nonzero modulus. -/
def threePrimeLocalFactor (p : ℕ) [NeZero p] (u : ZMod p) : ℝ :=
  (p : ℝ) * (threePrimeLocalPairs p u).card / ((p : ℝ) - 1) ^ 3

/-- The exact local factor of the ternary prime singular series. -/
theorem threePrimeLocalFactor_eq (p : ℕ) [NeZero p] (hp : 2 ≤ p)
    (u : ZMod p) :
    threePrimeLocalFactor p u =
      if u = 0 then 1 - 1 / ((p : ℝ) - 1) ^ 2
      else 1 + 1 / ((p : ℝ) - 1) ^ 3 := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hden : (p : ℝ) - 1 ≠ 0 := by linarith
  rw [threePrimeLocalFactor, threePrimeLocalPairs_card_real p hp u]
  split_ifs <;> field_simp <;> ring

/-- The natural-number formulation distinguishes primes dividing the target. -/
theorem threePrimeLocalFactor_natCast (p u : ℕ) [NeZero p] (hp : 2 ≤ p) :
    threePrimeLocalFactor p (u : ZMod p) =
      if p ∣ u then 1 - 1 / ((p : ℝ) - 1) ^ 2
      else 1 + 1 / ((p : ℝ) - 1) ^ 3 := by
  rw [threePrimeLocalFactor_eq p hp]
  simp only [ZMod.natCast_eq_zero_iff]

/-- An odd target has the positive factor two at the prime two. -/
theorem threePrimeLocalFactor_two (u : ℕ) (hu : Odd u) :
    threePrimeLocalFactor 2 (u : ZMod 2) = 2 := by
  rw [threePrimeLocalFactor_natCast 2 u (by omega)]
  have hnot : ¬2 ∣ u := by
    rw [← ZMod.natCast_eq_zero_iff]
    exact ZMod.natCast_ne_zero_iff_odd.mpr hu
  norm_num [hnot]

/-- The literal ordered triples underlying the local density. -/
def threePrimeLocalTriples (p : ℕ) [NeZero p] (u : ZMod p) :
    Finset (ZMod p × ZMod p × ZMod p) :=
  Finset.univ.filter (fun t =>
    t.1 ≠ 0 ∧ t.2.1 ≠ 0 ∧ t.2.2 ≠ 0 ∧ t.1 + t.2.1 + t.2.2 = u)

/-- The third residue is uniquely determined by the first two. -/
theorem threePrimeLocalTriples_eq_image (p : ℕ) [NeZero p] (u : ZMod p) :
    threePrimeLocalTriples p u =
      (threePrimeLocalPairs p u).image (fun t => (t.1, t.2, u - t.1 - t.2)) := by
  classical
  ext t
  rcases t with ⟨x, y, z⟩
  constructor
  · intro ht
    obtain ⟨hx, hy, hz, hsum⟩ := (Finset.mem_filter.mp ht).2
    have hthird : u - x - y = z := by linear_combination -hsum
    refine Finset.mem_image.mpr ⟨(x, y), ?_, ?_⟩
    · exact (mem_threePrimeLocalPairs u x y).mpr ⟨hx, hy, by simpa [hthird] using hz⟩
    · simp [hthird]
  · intro ht
    obtain ⟨⟨a, b⟩, hab, h⟩ := Finset.mem_image.mp ht
    obtain ⟨hx, hy, hz⟩ := (mem_threePrimeLocalPairs u a b).mp hab
    rw [← h]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, hx, hy, hz, ?_⟩
    ring

/-- The two-coordinate parametrization does not change the local count. -/
theorem threePrimeLocalTriples_card (p : ℕ) [NeZero p] (u : ZMod p) :
    (threePrimeLocalTriples p u).card = (threePrimeLocalPairs p u).card := by
  rw [threePrimeLocalTriples_eq_image]
  apply Finset.card_image_of_injective
  intro a b h
  apply Prod.ext
  · exact congrArg (fun t : ZMod p × ZMod p × ZMod p => t.1) h
  · exact congrArg (fun t : ZMod p × ZMod p × ZMod p => t.2.1) h

/-- For a prime modulus, the nonzero residue condition is exactly the unit
condition used in the prime singular series. -/
theorem mem_threePrimeLocalTriples_iff_units (p : ℕ) [Fact p.Prime]
    (u : ZMod p) (t : ZMod p × ZMod p × ZMod p) :
    t ∈ threePrimeLocalTriples p u ↔
      IsUnit t.1 ∧ IsUnit t.2.1 ∧ IsUnit t.2.2 ∧ t.1 + t.2.1 + t.2.2 = u := by
  simp [threePrimeLocalTriples, isUnit_iff_ne_zero]

/-- There is no local obstruction at a modulus of at least three when only
nonzero residue classes are required. -/
theorem threePrimeLocalPairs_card_pos (p : ℕ) [NeZero p] (hp : 3 ≤ p)
    (u : ZMod p) : 0 < (threePrimeLocalPairs p u).card := by
  rw [threePrimeLocalPairs_card p (by omega) u]
  have hp1 : 0 < p - 1 := by omega
  have hp2 : 0 < p - 2 := by omega
  split_ifs <;> positivity

/-- In particular every odd-prime local density is strictly positive. -/
theorem threePrimeLocalFactor_pos_of_three_le (p : ℕ) [NeZero p]
    (hp : 3 ≤ p) (u : ZMod p) : 0 < threePrimeLocalFactor p u := by
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hcard : (0 : ℝ) < (threePrimeLocalPairs p u).card := by
    exact_mod_cast threePrimeLocalPairs_card_pos p hp u
  dsimp [threePrimeLocalFactor]
  exact div_pos (mul_pos (by linarith) hcard) (pow_pos (by linarith) _)

/-- The only nonzero-residue ternary-sum obstruction is zero modulo two. -/
theorem threePrimeLocalTriples_nonempty_iff (p : ℕ) [NeZero p]
    (hp : 2 ≤ p) (u : ZMod p) :
    (threePrimeLocalTriples p u).Nonempty ↔ p ≠ 2 ∨ u ≠ 0 := by
  rw [← Finset.card_pos, threePrimeLocalTriples_card]
  by_cases hp2 : p = 2
  · subst p
    rw [threePrimeLocalPairs_card 2 (by omega)]
    by_cases hu : u = 0 <;> simp [hu]
  · have hpos := threePrimeLocalPairs_card_pos p (by omega) u
    simp [hp2, hpos]

/-- Every prime local factor is positive for odd natural targets. -/
theorem threePrimeLocalFactor_pos (p u : ℕ) [Fact p.Prime] (hu : Odd u) :
    0 < threePrimeLocalFactor p (u : ZMod p) := by
  have hp := (Fact.out : p.Prime).two_le
  by_cases hp2 : p = 2
  · subst p
    rw [threePrimeLocalFactor_two u hu]
    norm_num
  · exact threePrimeLocalFactor_pos_of_three_le p (by omega) _

/-- Oddness is exactly the local-solubility condition for a sum of three unit
residue classes at every prime. This is only a local statement, not a theorem
that those residue classes lift simultaneously to three prime integers. -/
theorem threePrimeLocalSolubility_iff_odd (u : ℕ) :
    (∀ p : ℕ, p.Prime → ∃ x y z : ZMod p,
      IsUnit x ∧ IsUnit y ∧ IsUnit z ∧ x + y + z = (u : ZMod p)) ↔ Odd u := by
  constructor
  · intro h
    obtain ⟨x, y, z, hx, hy, hz, hsum⟩ := h 2 Nat.prime_two
    have hmem : (x, y, z) ∈ threePrimeLocalTriples 2 (u : ZMod 2) :=
      (mem_threePrimeLocalTriples_iff_units 2 _ _).mpr ⟨hx, hy, hz, hsum⟩
    have hnonzero := (threePrimeLocalTriples_nonempty_iff 2 (by omega) _).mp ⟨_, hmem⟩
    exact ZMod.natCast_ne_zero_iff_odd.mp (hnonzero.resolve_left (by simp))
  · intro hu p hp
    let : Fact p.Prime := ⟨hp⟩
    have hlocal : p ≠ 2 ∨ (u : ZMod p) ≠ 0 := by
      by_cases hp2 : p = 2
      · right
        subst p
        exact ZMod.natCast_ne_zero_iff_odd.mpr hu
      · exact Or.inl hp2
    obtain ⟨t, ht⟩ := (threePrimeLocalTriples_nonempty_iff p hp.two_le _).mpr hlocal
    exact ⟨t.1, t.2.1, t.2.2, (mem_threePrimeLocalTriples_iff_units p _ _).mp ht⟩

private lemma sum_zmod_zero_other (p : ℕ) [NeZero p] (hp : 1 ≤ p)
    (a b : ℝ) :
    (∑ u : ZMod p, if u = 0 then a else b) = ((p : ℝ) - 1) * b + a := by
  classical
  rw [← Finset.sum_erase_add (s := (Finset.univ : Finset (ZMod p)))
    (fun u => if u = 0 then a else b) (Finset.mem_univ 0)]
  have heq : (∑ u ∈ (Finset.univ : Finset (ZMod p)).erase 0,
      if u = 0 then a else b) =
      ∑ _u ∈ (Finset.univ : Finset (ZMod p)).erase 0, b := by
    apply Finset.sum_congr rfl
    intro u hu
    exact ite_eq_right (Finset.mem_erase.mp hu).1
  rw [heq]
  simp [Nat.cast_sub hp]

/-- The normalized local solution density has exact average one. -/
theorem sum_threePrimeLocalFactor (p : ℕ) [NeZero p] (hp : 2 ≤ p) :
    (∑ u : ZMod p, threePrimeLocalFactor p u) = (p : ℝ) := by
  simp_rw [threePrimeLocalFactor_eq p hp]
  rw [sum_zmod_zero_other p (by omega)]
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hden : (p : ℝ) - 1 ≠ 0 := by linarith
  field_simp
  ring

/-- Exact local variance of the ternary density: after dividing by the number
of residues, it is `(p - 1)⁻⁵`. -/
theorem sum_threePrimeLocalFactor_centered_sq (p : ℕ) [NeZero p] (hp : 2 ≤ p) :
    (∑ u : ZMod p, (threePrimeLocalFactor p u - 1) ^ 2) =
      (p : ℝ) / ((p : ℝ) - 1) ^ 5 := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hden : (p : ℝ) - 1 ≠ 0 := by linarith
  have heq (u : ZMod p) : (threePrimeLocalFactor p u - 1) ^ 2 =
      if u = 0 then 1 / ((p : ℝ) - 1) ^ 4 else 1 / ((p : ℝ) - 1) ^ 6 := by
    rw [threePrimeLocalFactor_eq p hp]
    split_ifs <;> field_simp <;> ring
  simp_rw [heq]
  rw [sum_zmod_zero_other p (by omega)]
  field_simp
  ring

/-- The exact uncentered second moment, useful with the independent CRT
multiplicativity of local densities. -/
theorem sum_threePrimeLocalFactor_sq (p : ℕ) [NeZero p] (hp : 2 ≤ p) :
    (∑ u : ZMod p, (threePrimeLocalFactor p u) ^ 2) =
      (p : ℝ) * (1 + 1 / ((p : ℝ) - 1) ^ 5) := by
  have heq (u : ZMod p) : (threePrimeLocalFactor p u) ^ 2 =
      (threePrimeLocalFactor p u - 1) ^ 2 + 2 * threePrimeLocalFactor p u - 1 := by
    ring
  simp_rw [heq]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    sum_threePrimeLocalFactor p hp, sum_threePrimeLocalFactor_centered_sq p hp]
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]
  ring

end Problem337

end

end OAI
