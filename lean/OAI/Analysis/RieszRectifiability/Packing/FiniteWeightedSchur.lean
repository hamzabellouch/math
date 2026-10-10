import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.MeasureBounds

namespace OAI

namespace RieszRectifiability

noncomputable section

theorem weighted_young_real (x y u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    2 * x * y ≤ x ^ 2 * v / u + y ^ 2 * u / v := by
  have heq : (x ^ 2 * v / u + y ^ 2 * u / v - 2 * x * y) * (u * v) =
      (v * x - u * y) ^ 2 := by
    field_simp
    ring
  have hp := sq_nonneg (v * x - u * y)
  rw [← heq] at hp
  have hnonneg : 0 ≤ x ^ 2 * v / u + y ^ 2 * u / v - 2 * x * y :=
    nonneg_of_mul_nonneg_left hp (mul_pos hu hv)
  linarith

theorem finite_weighted_schur_quadratic {ι : Type*} (s : Finset ι)
    (k : ι → ι → ℝ) (w a : ι → ℝ) (C : ℝ)
    (hw : ∀ i ∈ s, 0 < w i) (hk : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ k i j)
    (hsymm : ∀ i ∈ s, ∀ j ∈ s, k j i = k i j)
    (hrow : ∀ i ∈ s, ∑ j ∈ s, k i j * w j ≤ C * w i) :
    (∑ i ∈ s, ∑ j ∈ s, |a i| * |a j| * k i j) ≤ C * ∑ i ∈ s, a i ^ 2 := by
  have hpoint (i : ι) (hi : i ∈ s) (j : ι) (hj : j ∈ s) :
      2 * (|a i| * |a j| * k i j) ≤
        a i ^ 2 * k i j * w j / w i + a j ^ 2 * k i j * w i / w j := by
    have hy := weighted_young_real |a i| |a j| (w i) (w j) (hw i hi) (hw j hj)
    simp only [sq_abs] at hy
    calc
      _ = (2 * |a i| * |a j|) * k i j := by ring
      _ ≤ (a i ^ 2 * w j / w i + a j ^ 2 * w i / w j) * k i j :=
        mul_le_mul_of_nonneg_right hy (hk i hi j hj)
      _ = _ := by ring
  let A : ℝ := ∑ i ∈ s, ∑ j ∈ s, a i ^ 2 * k i j * w j / w i
  let B : ℝ := ∑ i ∈ s, ∑ j ∈ s, a j ^ 2 * k i j * w i / w j
  have hA : A ≤ C * ∑ i ∈ s, a i ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    calc
      _ = (a i ^ 2 / w i) * (∑ j ∈ s, k i j * w j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ (a i ^ 2 / w i) * (C * w i) :=
        mul_le_mul_of_nonneg_left (hrow i hi) (div_nonneg (sq_nonneg _) (hw i hi).le)
      _ = C * a i ^ 2 := by field_simp [(hw i hi).ne']
  have hBA : B = A := by
    dsimp only [A, B]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hsymm i hi j hj]
  have hh := Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => hpoint i hi j hj))
  have htwo : 2 * (∑ i ∈ s, ∑ j ∈ s, |a i| * |a j| * k i j) ≤ A + B := by
    simpa only [A, B, Finset.sum_add_distrib, Finset.mul_sum] using! hh
  rw [hBA] at htwo
  linarith

end

end RieszRectifiability

end OAI
