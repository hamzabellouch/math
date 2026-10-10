import Mathlib

namespace OAI

/-!
# Exponent contradictions in the exceptional character moments

These are the real-variable steps in the proof of the exceptional-character-moment proposition
(`prop:dual`) in *An unconditional first moment for cubic Gauss sums*.  The analytic
large-sieve and Gram estimates are separate inputs to these numerical
steps.
-/

namespace CubicFirstMoment

/-- On the useful range, the mixed term in the cubic sieve dominates both
endpoint terms. -/
theorem cubicSieve_exponent {z : ℝ} (hz₀ : 1 / 2 ≤ z) (hz₁ : z ≤ 2) :
    z + max (max 1 z) (2 * (1 + z) / 3) = 2 / 3 + 5 * z / 3 := by
  have h₁ : 1 ≤ 2 * (1 + z) / 3 := by linarith
  have h₂ : z ≤ 2 * (1 + z) / 3 := by linarith
  rw [max_eq_right (max_le h₁ h₂)]
  ring

/-- Cardinality and the fourth moment force saturation in the balanced
exceptional configuration. -/
theorem balanced_moment_saturation {r v : ℝ}
    (hlarge : 7 / 3 - 2 * v ≤ r) (hcard : r ≤ 2 / 3)
    (hfourth : r + 4 * v ≤ 4) : r = 2 / 3 ∧ v = 5 / 6 := by
  constructor <;> linarith

/-- Repeating an intermediate factor improves the balanced fourth-moment
bound strictly beyond the saturated row count. -/
theorem balanced_extra_factor_gap {z : ℝ} (hz₀ : 1 < z) (hz₁ : z < 2) :
    max (4 / 3) z - 2 * z / 3 < 2 / 3 := by
  rcases le_total (4 / 3 : ℝ) z with h | h
  · rw [max_eq_right h]
    linarith
  · rw [max_eq_left h]
    linarith

/-- The diagonal and off-diagonal Gram exponents are both strictly below
the putative large-value exponent when `4/3 < z < 2`. -/
theorem gram_exponent_gap {z : ℝ} (hz₀ : 4 / 3 < z) (hz₁ : z < 2) :
    max (z - 2 / 3) ((z + max 1 (2 - 2 * z / 3) - 2 / 3) / 2) <
      2 * z / 3 := by
  apply max_lt
  · linarith
  · rcases le_total (1 : ℝ) (2 - 2 * z / 3) with h | h
    · rw [max_eq_right h]
      linarith
    · rw [max_eq_left h]
      linarith

/-- A positive short factor can be copied a fixed integer number of times
so that its exponent is strictly inside the Gram range. -/
theorem exists_copies_in_gram_range {a : ℝ} (ha : 0 < a) (ha₁ : a ≤ 1 / 2) :
    ∃ m : ℕ, 4 / 3 < (m : ℝ) * a ∧ (m : ℝ) * a < 2 := by
  let q : ℝ := (4 / 3) / a
  let m : ℕ := ⌊q⌋₊ + 1
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hlower : q < (m : ℝ) := by
    simpa [m] using Nat.lt_floor_add_one q
  have hupper : (m : ℝ) ≤ q + 1 := by
    dsimp [m]
    push_cast
    linarith [Nat.floor_le hq]
  have hqa : q * a = 4 / 3 := by
    dsimp [q]
    exact div_mul_cancel₀ _ ha.ne'
  refine ⟨m, ?_, ?_⟩
  · nlinarith [mul_lt_mul_of_pos_right hlower ha]
  · nlinarith [mul_le_mul_of_nonneg_right hupper ha.le]

/-- The all-ones multiplicity vector and the vector with one extra copy
force that factor's defect to be nonpositive. -/
theorem multiplicity_defect_nonpos {r total defect : ℝ}
    (hlower : 2 / 3 - 2 * total ≤ r)
    (hextra : r ≤ 2 / 3 - 2 * (total + defect)) : defect ≤ 0 := by
  linarith

/-- When deleting a short factor stays in the sieve range, the two
multiplicity tests force its defect to vanish. -/
theorem short_multiplicity_defect_zero {r total defect : ℝ}
    (hlower : 2 / 3 - 2 * total ≤ r)
    (hextra : r ≤ 2 / 3 - 2 * (total + defect))
    (hdelete : r ≤ 2 / 3 - 2 * (total - defect)) : defect = 0 := by
  linarith

end CubicFirstMoment
open scoped BigOperators

namespace CubicFirstMoment

private theorem sum_omit_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → ℝ) (j : ι) :
    (∑ i, if i = j then 0 else v i) = (∑ i, v i) - v j := by
  calc
    _ = ∑ i, (v i - if i = j then v i else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp_all
    _ = _ := by simp [Finset.sum_sub_distrib]

/-- The fixed-multiplicity argument in the first exceptional configuration.
It forces every factor to have the same `5/6` exponent and forces the row
count exponent to be `2/3`, before the off-diagonal Gram estimate is applied.

Here `d i` is `v i - 5 * a i / 6`. The two sides of the large-value and
large-sieve inequalities have already been expressed in terms of these
factor defects. -/
theorem exceptional_multiplicity_rigidity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a d : ι → ℝ) (r : ℝ)
    (ha : ∀ i, 0 ≤ a i ∧ a i < 1) (hsum : ∑ i, a i = 1)
    (hlarge : 2 / 3 - 2 * (∑ i, d i) ≤ r)
    (hmoment : ∀ k : ι → ℕ,
      1 / 2 ≤ (∑ i, (k i : ℝ) * a i) → (∑ i, (k i : ℝ) * a i) ≤ 2 →
      r ≤ 2 / 3 - 2 * (∑ i, (k i : ℝ) * d i)) :
    (∀ i, d i = 0) ∧ r = 2 / 3 := by
  have hnonpos (j : ι) : d j ≤ 0 := by
    let k : ι → ℕ := fun i => 1 + if i = j then 1 else 0
    have hk (v : ι → ℝ) : (∑ i, (k i : ℝ) * v i) = (∑ i, v i) + v j := by
      simp [k, add_mul, Finset.sum_add_distrib]
    have hbound := hmoment k (by rw [hk, hsum]; linarith [(ha j).1])
      (by rw [hk, hsum]; linarith [(ha j).2])
    rw [hk] at hbound
    exact multiplicity_defect_nonpos hlarge hbound
  have hshort (j : ι) (hj : a j ≤ 1 / 2) : d j = 0 := by
    let k : ι → ℕ := fun i => if i = j then 0 else 1
    have hk (v : ι → ℝ) : (∑ i, (k i : ℝ) * v i) = (∑ i, v i) - v j := by
      simpa [k] using sum_omit_one v j
    have hbound := hmoment k (by rw [hk, hsum]; linarith)
      (by rw [hk, hsum]; linarith [(ha j).1])
    rw [hk] at hbound
    linarith [hnonpos j]
  have hzero : ∀ i, d i = 0 := by
    by_cases hall : ∀ i, a i ≤ 1 / 2
    · exact fun i => hshort i (hall i)
    · push Not at hall
      obtain ⟨j, hj⟩ := hall
      have hothers (i : ι) (hij : i ≠ j) : d i = 0 := by
        apply hshort
        have hsmall : a i ≤ ∑ k ∈ (Finset.univ : Finset ι).erase j, a k :=
          Finset.single_le_sum (fun k _ => (ha k).1) (by simp [hij])
        have hrest := Finset.sum_erase_add (Finset.univ : Finset ι) a (Finset.mem_univ j)
        rw [hsum] at hrest
        linarith
      have htotal : (∑ i, d i) = d j := by
        apply Finset.sum_eq_single j
        · intro i _ hij
          exact hothers i hij
        · simp
      obtain ⟨m, hm₀, hm₁⟩ := exists_copies_in_gram_range
        (a := 1 - a j) (by linarith [(ha j).2]) (by linarith)
      let k : ι → ℕ := fun i => if i = j then 0 else m
      have hka : (∑ i, (k i : ℝ) * a i) = (m : ℝ) * (1 - a j) := by
        calc
          _ = (m : ℝ) * ∑ i, (if i = j then 0 else a i) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            simp only [k]
            split_ifs <;> simp
          _ = _ := by rw [sum_omit_one, hsum]
      have hkd : (∑ i, (k i : ℝ) * d i) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        by_cases hij : i = j
        · simp [k, hij]
        · simp [k, hij, hothers i hij]
      have hbound := hmoment k (by rw [hka]; linarith) (by rw [hka]; linarith)
      rw [hkd, mul_zero, sub_zero] at hbound
      have hdj : d j = 0 := by
        rw [htotal] at hlarge
        linarith [hnonpos j]
      intro i
      by_cases hij : i = j
      · simpa [hij] using hdj
      · exact hothers i hij
  refine ⟨hzero, ?_⟩
  have htotal : (∑ i, d i) = 0 := by simp [hzero]
  rw [htotal, mul_zero, sub_zero] at hlarge
  have hone := hmoment (fun _ => 1) (by norm_num [hsum]) (by norm_num [hsum])
  have hupper : r ≤ 2 / 3 := by simpa [hzero] using hone
  exact le_antisymm hupper hlarge

end CubicFirstMoment
namespace CubicFirstMoment

/-- In the balanced exceptional configuration, a saturated total value
forces at least one positive-length factor to attain its `5/6` share.
This is the factor that is repeated in the extra-moment argument. -/
theorem exists_balanced_factor {ι : Type*} [Fintype ι]
    (a v : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hv : ∀ i, v i ≤ a i)
    (ha_sum : ∑ i, a i = 1) (hv_sum : ∑ i, v i = 5 / 6) :
    ∃ i, 0 < a i ∧ 5 * a i / 6 ≤ v i := by
  classical
  by_contra! hn
  have hle (i : ι) : v i ≤ 5 * a i / 6 := by
    by_cases hi : 0 < a i
    · exact (hn i hi).le
    · have hz : a i = 0 := le_antisymm (not_lt.mp hi) (ha i)
      simpa [hz] using hv i
  have hex : ∃ i, 0 < a i := by
    by_contra! h
    have hs : (∑ i, a i) ≤ 0 := Finset.sum_nonpos (fun i _ => h i)
    linarith
  obtain ⟨j, hj⟩ := hex
  have hs : (∑ i, v i) < ∑ i, 5 * a i / 6 :=
    Finset.sum_lt_sum (fun i _ => hle i) ⟨j, Finset.mem_univ j, hn j hj⟩
  have heq : (∑ i, 5 * a i / 6) = 5 / 6 := by
    rw [← Finset.sum_div, ← Finset.mul_sum, ha_sum]
    norm_num
  linarith

end CubicFirstMoment

end OAI
