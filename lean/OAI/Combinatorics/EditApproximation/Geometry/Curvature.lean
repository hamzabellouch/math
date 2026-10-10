import Mathlib

namespace OAI

/-!
# Cost-weighted curvature

Finite weighted variance and the local energy telescope from Section 6
of the edit-distance manuscript. Zero child masses are allowed, with the
length-gap invariant forcing their length gaps to vanish.
-/

namespace EditApproximation

open Finset

theorem weighted_variance_identity {ι : Type*} (children : Finset ι)
    (mass gap : ι → ℝ)
    (hzero : ∀ i ∈ children, mass i = 0 → gap i = 0)
    (hW : 0 < ∑ i ∈ children, mass i) :
    (∑ i ∈ children, gap i ^ 2 / mass i) -
        (∑ i ∈ children, gap i) ^ 2 / (∑ i ∈ children, mass i) =
      ∑ i ∈ children,
        (gap i - ((∑ j ∈ children, gap j) / (∑ j ∈ children, mass j)) * mass i) ^ 2 /
          mass i := by
  let v := (∑ i ∈ children, gap i) / (∑ i ∈ children, mass i)
  have hterm (i : ι) (hi : i ∈ children) :
      (gap i - v * mass i) ^ 2 / mass i =
        gap i ^ 2 / mass i - 2 * v * gap i + v ^ 2 * mass i := by
    by_cases hz : mass i = 0
    · simp only [hz, hzero i hi hz, mul_zero, zero_pow (by omega : 2 ≠ 0),
        zero_div, sub_self, zero_add]
    · field_simp
      ring
  have hsum := sum_congr rfl hterm
  rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum] at hsum
  rw [hsum]
  dsimp [v]
  field_simp
  ring

theorem curvature_nonneg {ι : Type*} (children : Finset ι)
    (mass gap : ι → ℝ)
    (hmass : ∀ i ∈ children, 0 ≤ mass i)
    (hzero : ∀ i ∈ children, mass i = 0 → gap i = 0)
    (hW : 0 < ∑ i ∈ children, mass i) :
    0 ≤ (∑ i ∈ children, gap i ^ 2 / mass i) -
      (∑ i ∈ children, gap i) ^ 2 / (∑ i ∈ children, mass i) := by
  rw [weighted_variance_identity children mass gap hzero hW]
  exact sum_nonneg fun i hi => div_nonneg (sq_nonneg _) (hmass i hi)

/-- Weighted Cauchy--Schwarz controls the total absolute deviation by
the curvature times the total warmup mass. -/
theorem curvature_l1_squared_le {ι : Type*} (children : Finset ι)
    (mass gap : ι → ℝ)
    (hmass : ∀ i ∈ children, 0 ≤ mass i)
    (hzero : ∀ i ∈ children, mass i = 0 → gap i = 0)
    (hW : 0 < ∑ i ∈ children, mass i) :
    (∑ i ∈ children,
      |gap i - ((∑ j ∈ children, gap j) / (∑ j ∈ children, mass j)) * mass i|) ^ 2 ≤
      (∑ i ∈ children, mass i) *
        ((∑ i ∈ children, gap i ^ 2 / mass i) -
          (∑ i ∈ children, gap i) ^ 2 / (∑ i ∈ children, mass i)) := by
  let v := (∑ i ∈ children, gap i) / (∑ i ∈ children, mass i)
  have hterm (i : ι) (hi : i ∈ children) :
      |gap i - v * mass i| ^ 2 ≤ mass i * ((gap i - v * mass i) ^ 2 / mass i) := by
    by_cases hz : mass i = 0
    · simp only [hz, hzero i hi hz, mul_zero, sub_zero, abs_zero,
        zero_pow (by omega : 2 ≠ 0), zero_div, le_refl]
    · rw [sq_abs]
      exact le_of_eq (by field_simp)
  have hcs := sum_sq_le_sum_mul_sum_of_sq_le_mul children hmass
    (fun i hi => div_nonneg (sq_nonneg (gap i - v * mass i)) (hmass i hi)) hterm
  rw [weighted_variance_identity children mass gap hzero hW]
  exact hcs

theorem curvature_l1_le_sqrt {ι : Type*} (children : Finset ι)
    (mass gap : ι → ℝ)
    (hmass : ∀ i ∈ children, 0 ≤ mass i)
    (hzero : ∀ i ∈ children, mass i = 0 → gap i = 0)
    (hW : 0 < ∑ i ∈ children, mass i) :
    (∑ i ∈ children,
      |gap i - ((∑ j ∈ children, gap j) / (∑ j ∈ children, mass j)) * mass i|) ≤
      Real.sqrt ((∑ i ∈ children, mass i) *
        ((∑ i ∈ children, gap i ^ 2 / mass i) -
          (∑ i ∈ children, gap i) ^ 2 / (∑ i ∈ children, mass i))) := by
  apply (sq_le_sq₀ (sum_nonneg fun _ _ => abs_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (mul_nonneg hW.le (curvature_nonneg children mass gap hmass hzero hW))]
  exact curvature_l1_squared_le children mass gap hmass hzero hW

/-- The parent/rounded-parent energy discrepancy is controlled by endpoint
movement and the negative part of the parent-minus-child mass discrepancy. -/
theorem local_energy_discrepancy {parentMass childMass parentGap roundedGap movement : ℝ}
    (hp : 0 < parentMass) (hc : 0 < childMass)
    (hparent : |parentGap| ≤ parentMass)
    (hchild : |roundedGap| ≤ childMass)
    (hmove : |parentGap - roundedGap| ≤ movement)
    (hsmall : movement ≤ parentMass) :
    parentGap ^ 2 / parentMass - roundedGap ^ 2 / childMass ≤
      3 * movement + 2 * max (childMass - parentMass) 0 := by
  have he : 0 ≤ movement := (abs_nonneg _).trans hmove
  have hrounded : |roundedGap| ≤ 2 * parentMass := by
    have ht := abs_add_le parentGap (roundedGap - parentGap)
    have hdiff : |roundedGap - parentGap| ≤ movement := by
      simpa only [abs_sub_comm] using hmove
    have hid : parentGap + (roundedGap - parentGap) = roundedGap := by ring
    rw [hid] at ht
    linarith
  have hsum : |parentGap + roundedGap| ≤ 3 * parentMass :=
    (abs_add_le _ _).trans (by linarith)
  have hnum : parentGap ^ 2 - roundedGap ^ 2 ≤ 3 * movement * parentMass := by
    have hfactor : parentGap ^ 2 - roundedGap ^ 2 =
        (parentGap - roundedGap) * (parentGap + roundedGap) := by ring
    rw [hfactor]
    apply (le_abs_self _).trans
    rw [abs_mul]
    have hmul := mul_le_mul hmove hsum (abs_nonneg _) he
    nlinarith
  have hfirst : (parentGap ^ 2 - roundedGap ^ 2) / parentMass ≤ 3 * movement :=
    (div_le_iff₀ hp).2 hnum
  have hsecond : roundedGap ^ 2 * (childMass - parentMass) / (parentMass * childMass) ≤
      2 * max (childMass - parentMass) 0 := by
    by_cases hle : childMass ≤ parentMass
    · have hnumle : roundedGap ^ 2 * (childMass - parentMass) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (by linarith)
      have hdivle := div_nonpos_of_nonpos_of_nonneg hnumle (mul_pos hp hc).le
      exact hdivle.trans (by positivity)
    · have hdiff : 0 ≤ childMass - parentMass := by linarith
      have hsq : roundedGap ^ 2 ≤ 2 * parentMass * childMass := by
        have hmul := mul_le_mul hrounded hchild (abs_nonneg _) (by positivity)
        simpa only [← pow_two, sq_abs] using hmul
      rw [max_eq_left hdiff]
      apply (div_le_iff₀ (mul_pos hp hc)).2
      have hmul := mul_le_mul_of_nonneg_right hsq hdiff
      nlinarith
  have hid : parentGap ^ 2 / parentMass - roundedGap ^ 2 / childMass =
      (parentGap ^ 2 - roundedGap ^ 2) / parentMass +
        roundedGap ^ 2 * (childMass - parentMass) / (parentMass * childMass) := by
    field_simp
    ring
  rw [hid]
  linarith

end EditApproximation

end OAI
