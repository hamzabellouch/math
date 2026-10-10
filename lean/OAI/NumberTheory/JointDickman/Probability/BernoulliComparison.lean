import OAI.NumberTheory.JointDickman.Arithmetic.PrimeSetWeights

namespace OAI

/-!
# Mutually exclusive site hits versus independent Bernoulli hits

At one prime the actual site hits are mutually exclusive. Their categorical
law differs from independent Bernoulli hits by at most twice the square of
the sum of the site probabilities in `L¹`. Everything here is a finite-sum
proof; no coupling estimate is assumed.
-/

namespace JointDickman

open scoped BigOperators

/-- Empty hit set with mass `1-sum q`, singleton `{i}` with mass `q i`,
and zero on every other subset. The delta-sum form avoids any choices. -/
noncomputable def categoricalSubsetMass {α : Type*} [DecidableEq α]
    (P : Finset α) (q : α → ℝ) (S : Finset α) : ℝ :=
  (if S = ∅ then 1 - ∑ i ∈ P, q i else 0) +
    ∑ i ∈ P, if S = {i} then q i else 0

private theorem sum_singleton_kernel {α : Type*} [DecidableEq α]
    (P : Finset α) (w : α → ℝ) :
    (∑ S ∈ P.powerset, ∑ i ∈ P, if S = {i} then w i else 0) = ∑ i ∈ P, w i := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp [Finset.mem_powerset, Finset.singleton_subset_iff, hi]

@[simp] theorem categoricalSubsetMass_empty {α : Type*} [DecidableEq α]
    (P : Finset α) (q : α → ℝ) :
    categoricalSubsetMass P q ∅ = 1 - ∑ i ∈ P, q i := by
  simp [categoricalSubsetMass]

theorem categoricalSubsetMass_singleton {α : Type*} [DecidableEq α]
    {P : Finset α} (q : α → ℝ) {i : α} (hi : i ∈ P) :
    categoricalSubsetMass P q {i} = q i := by
  classical
  simp [categoricalSubsetMass, Finset.singleton_inj, hi]

theorem categoricalSubsetMass_sum {α : Type*} [DecidableEq α]
    (P : Finset α) (q : α → ℝ) :
    ∑ S ∈ P.powerset, categoricalSubsetMass P q S = 1 := by
  classical
  unfold categoricalSubsetMass
  rw [Finset.sum_add_distrib, sum_singleton_kernel]
  simp

theorem categoricalSubsetMass_nonneg {α : Type*} [DecidableEq α]
    {P S : Finset α} {q : α → ℝ} (hq : ∀ i ∈ P, 0 ≤ q i)
    (hsum : ∑ i ∈ P, q i ≤ 1) : 0 ≤ categoricalSubsetMass P q S := by
  unfold categoricalSubsetMass
  apply add_nonneg
  · split_ifs <;> linarith
  · exact Finset.sum_nonneg (fun i hi => by split_ifs <;> simp_all)

private theorem complement_product_lower {α : Type*} [DecidableEq α]
    (P : Finset α) (q : α → ℝ) (hq : ∀ i ∈ P, 0 ≤ q i ∧ q i ≤ 1) :
    1 - ∑ i ∈ P, q i ≤ ∏ i ∈ P, (1 - q i) := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | @insert i P hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    have hqi := hq i (Finset.mem_insert_self _ _)
    have hqP : ∀ j ∈ P, 0 ≤ q j ∧ q j ≤ 1 := fun j hj => hq j (Finset.mem_insert_of_mem hj)
    have hmul := mul_le_mul_of_nonneg_left (ih hqP) (sub_nonneg.mpr hqi.2)
    have hsum0 : 0 ≤ ∑ j ∈ P, q j := Finset.sum_nonneg (fun j hj => (hqP j hj).1)
    nlinarith

private theorem bernoulli_singleton_le {α : Type*} [DecidableEq α]
    {P : Finset α} {q : α → ℝ} (hq : ∀ i ∈ P, 0 ≤ q i ∧ q i ≤ 1)
    {i : α} (hi : i ∈ P) : bernoulliSubsetMass P q {i} ≤ q i := by
  have hp : (∏ j ∈ P \ {i}, (1 - q j)) ≤ 1 := by
    apply Finset.prod_le_one₀
    · intro j hj
      exact sub_nonneg.mpr (hq j (Finset.mem_sdiff.mp hj).1).2
    · intro j hj
      linarith [(hq j (Finset.mem_sdiff.mp hj).1).1]
  simpa [bernoulliSubsetMass] using mul_le_mul_of_nonneg_left hp (hq i hi).1

private theorem singleton_deficit_le {α : Type*} [DecidableEq α]
    {P : Finset α} {q : α → ℝ} (hq : ∀ i ∈ P, 0 ≤ q i ∧ q i ≤ 1)
    {i : α} (hi : i ∈ P) :
    q i - bernoulliSubsetMass P q {i} ≤ q i * (∑ j ∈ P, q j) := by
  have hqsub : ∀ j ∈ P \ {i}, 0 ≤ q j ∧ q j ≤ 1 :=
    fun j hj => hq j (Finset.mem_sdiff.mp hj).1
  have hprod := complement_product_lower (P \ {i}) q hqsub
  have hsum : (∑ j ∈ P \ {i}, q j) ≤ ∑ j ∈ P, q j :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
      (fun j hj _ => (hq j hj).1)
  have hmul := mul_le_mul_of_nonneg_left hprod (hq i hi).1
  have hmul' := mul_le_mul_of_nonneg_left hsum (hq i hi).1
  simp only [bernoulliSubsetMass, Finset.prod_singleton] at *
  nlinarith

/-- An exact identity: twice the total singleton deficit is the entire
`L¹` discrepancy. The empty-set excess and multi-hit mass balance it. -/
theorem categorical_bernoulli_l1_eq {α : Type*} [DecidableEq α]
    (P : Finset α) (q : α → ℝ) (hq : ∀ i ∈ P, 0 ≤ q i ∧ q i ≤ 1) :
    (∑ S ∈ P.powerset, |categoricalSubsetMass P q S - bernoulliSubsetMass P q S|) =
      2 * ∑ i ∈ P, (q i - bernoulliSubsetMass P q {i}) := by
  classical
  have hpoint (S : Finset α) (hS : S ∈ P.powerset) :
      |categoricalSubsetMass P q S - bernoulliSubsetMass P q S| =
      2 * (∑ i ∈ P, if S = {i} then q i - bernoulliSubsetMass P q {i} else 0) -
        (categoricalSubsetMass P q S - bernoulliSubsetMass P q S) := by
    by_cases hS0 : S = ∅
    · subst S
      have he := complement_product_lower P q hq
      simp only [categoricalSubsetMass_empty, bernoulliSubsetMass, Finset.prod_empty,
        Finset.sdiff_empty, one_mul] at *
      rw [abs_of_nonpos (by linarith)]
      simp
    · by_cases hs : ∃ i ∈ P, S = {i}
      · obtain ⟨i, hi, rfl⟩ := hs
        rw [categoricalSubsetMass_singleton q hi,
          abs_of_nonneg (sub_nonneg.mpr (bernoulli_singleton_le hq hi))]
        simp only [Finset.singleton_inj]
        simp [hi]
        ring
      · have hne (i : α) (hi : i ∈ P) : S ≠ {i} := fun heq => hs ⟨i, hi, heq⟩
        have hcat : categoricalSubsetMass P q S = 0 := by
          simp only [categoricalSubsetMass, ite_eq_right hS0, zero_add]
          exact Finset.sum_eq_zero (fun i hi => by simp [hne i hi])
        have hd : (∑ i ∈ P, if S = {i} then q i - bernoulliSubsetMass P q {i} else 0) = 0 :=
          Finset.sum_eq_zero (fun i hi => by simp [hne i hi])
        rw [hcat, hd, zero_sub, abs_neg,
          abs_of_nonneg (bernoulliSubsetMass_nonneg (Finset.mem_powerset.mp hS) hq)]
        ring
  calc
    _ = ∑ S ∈ P.powerset,
        (2 * (∑ i ∈ P, if S = {i} then q i - bernoulliSubsetMass P q {i} else 0) -
          (categoricalSubsetMass P q S - bernoulliSubsetMass P q S)) :=
      Finset.sum_congr rfl hpoint
    _ = _ := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_singleton_kernel]
      simp only [Finset.sum_sub_distrib, categoricalSubsetMass_sum, bernoulliSubsetMass_sum]
      ring

/-- The finite categorical-to-independent comparison used at a single
prime. Its error is quadratic in the sum of the hit probabilities. -/
theorem categorical_bernoulli_l1_le {α : Type*} [DecidableEq α]
    (P : Finset α) (q : α → ℝ) (hq : ∀ i ∈ P, 0 ≤ q i ∧ q i ≤ 1) :
    (∑ S ∈ P.powerset, |categoricalSubsetMass P q S - bernoulliSubsetMass P q S|) ≤
      2 * (∑ i ∈ P, q i) ^ 2 := by
  rw [categorical_bernoulli_l1_eq P q hq]
  have h := Finset.sum_le_sum (s := P) (fun i hi => singleton_deficit_le hq hi)
  rw [← Finset.sum_mul] at h
  nlinarith

/-- Any bounded complex test inherits the same finite comparison bound. -/
theorem categorical_bernoulli_test_bound {α : Type*} [DecidableEq α]
    (P : Finset α) (q : α → ℝ) (hq : ∀ i ∈ P, 0 ≤ q i ∧ q i ≤ 1)
    (F : Finset α → ℂ) {L : ℝ} (hL : 0 ≤ L)
    (hF : ∀ S ∈ P.powerset, ‖F S‖ ≤ L) :
    ‖(∑ S ∈ P.powerset, (categoricalSubsetMass P q S : ℂ) * F S) -
      (∑ S ∈ P.powerset, (bernoulliSubsetMass P q S : ℂ) * F S)‖ ≤
      2 * L * (∑ i ∈ P, q i) ^ 2 := by
  rw [← Finset.sum_sub_distrib]
  have hnorm := norm_sum_le P.powerset
    (fun S => (categoricalSubsetMass P q S : ℂ) * F S -
      (bernoulliSubsetMass P q S : ℂ) * F S)
  refine hnorm.trans ?_
  calc
    _ ≤ ∑ S ∈ P.powerset,
        |categoricalSubsetMass P q S - bernoulliSubsetMass P q S| * L := by
      apply Finset.sum_le_sum
      intro S hS
      rw [← sub_mul, ← Complex.ofReal_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hF S hS) (abs_nonneg _)
    _ = (∑ S ∈ P.powerset,
        |categoricalSubsetMass P q S - bernoulliSubsetMass P q S|) * L := by
      rw [Finset.sum_mul]
    _ ≤ (2 * (∑ i ∈ P, q i) ^ 2) * L :=
      mul_le_mul_of_nonneg_right (categorical_bernoulli_l1_le P q hq) hL
    _ = _ := by ring

/-- Uniform site probabilities give the stated quadratic site-count loss. -/
theorem categorical_bernoulli_uniform_l1_le {α : Type*} [DecidableEq α]
    (P : Finset α) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (∑ S ∈ P.powerset,
      |categoricalSubsetMass P (fun _ => u) S - bernoulliSubsetMass P (fun _ => u) S|) ≤
      2 * (P.card : ℝ) ^ 2 * u ^ 2 := by
  have h := categorical_bernoulli_l1_le P (fun _ => u) (fun _ _ => ⟨hu0, hu1⟩)
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_pow, mul_assoc] using h

/-- At one prime `p`, the local error is at most `2 |P|²/p²`. -/
theorem categorical_bernoulli_prime_l1_le {α : Type*} [DecidableEq α]
    (P : Finset α) {p : ℕ} (hp : p.Prime) :
    (∑ S ∈ P.powerset,
      |categoricalSubsetMass P (fun _ => 1 / (p : ℝ)) S -
        bernoulliSubsetMass P (fun _ => 1 / (p : ℝ)) S|) ≤
      2 * (P.card : ℝ) ^ 2 / (p : ℝ) ^ 2 := by
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have h := categorical_bernoulli_uniform_l1_le P
    (by positivity : (0 : ℝ) ≤ 1 / (p : ℝ))
    ((div_le_one (by positivity : (0 : ℝ) < p)).mpr hpR)
  simpa only [div_pow, one_pow, mul_one_div] using h

/-- The mutually exclusive model is a genuine nonnegative probability
mass when the number of sites is at most the prime. -/
theorem categorical_prime_mass_nonneg {α : Type*} [DecidableEq α]
    (P S : Finset α) {p : ℕ} (hp : p.Prime) (hcard : P.card ≤ p) :
    0 ≤ categoricalSubsetMass P (fun _ => 1 / (p : ℝ)) S := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  apply categoricalSubsetMass_nonneg
  · intro i hi
    positivity
  · simp only [Finset.sum_const, nsmul_eq_mul, mul_one_div]
    exact (div_le_one hpR).mpr (by exact_mod_cast hcard)

end JointDickman

end OAI
