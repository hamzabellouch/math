import OAI.MathematicalPhysics.DefocusingNLS.Linear.SobolevTranslation
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SumIntegralComparisons

namespace OAI

/-! # Exact weights of the expanding-torus Sobolev norm

The norm from manuscript (lin:YL), after extracting `(2π)^12`, has squared
Fourier weight `L^(2a) ⟨n⟩^(12-2a) + L^(12-2k) |n|^(2k)`.
The auxiliary one-dimensional weights will control its inverse sum.
-/

open Set MeasureTheory

namespace DefocusingNLS

noncomputable def expandingSobolevWeightSq (a k L : ℝ) (n : frequencyLattice) : ℝ :=
  L ^ (2 * a) * (1 + ‖n‖ ^ 2) ^ (6 - a) + L ^ (12 - 2 * k) * ‖n‖ ^ (2 * k)

noncomputable def expandingOneDimWeight (a k L x : ℝ) : ℝ :=
  L ^ (a / 6) * (1 + x ^ 2) ^ ((6 - a) / 12) +
    L ^ (1 - k / 6) * |x| ^ (k / 6)

noncomputable def expandingOneDimKernel (a k L x : ℝ) : ℝ :=
  (expandingOneDimWeight a k L x)⁻¹

theorem expandingSobolevWeightSq_pos (a k L : ℝ) (hL : 1 ≤ L) (n : frequencyLattice) :
    0 < expandingSobolevWeightSq a k L n := by
  unfold expandingSobolevWeightSq
  exact add_pos_of_pos_of_nonneg (mul_pos (Real.rpow_pos_of_pos (by linarith) _)
    (Real.rpow_pos_of_pos (by positivity) _)) (by positivity)

theorem expandingOneDimWeight_pos (a k L x : ℝ) (hL : 1 ≤ L) :
    0 < expandingOneDimWeight a k L x := by
  unfold expandingOneDimWeight
  exact add_pos_of_pos_of_nonneg (mul_pos (Real.rpow_pos_of_pos (by linarith) _)
    (Real.rpow_pos_of_pos (by positivity) _)) (by positivity)

theorem expandingOneDimKernel_nonneg (a k L x : ℝ) (hL : 1 ≤ L) :
    0 ≤ expandingOneDimKernel a k L x :=
  (inv_pos.mpr (expandingOneDimWeight_pos a k L x hL)).le

theorem expandingOneDimKernel_even (a k L x : ℝ) :
    expandingOneDimKernel a k L (-x) = expandingOneDimKernel a k L x := by
  simp [expandingOneDimKernel, expandingOneDimWeight]

theorem expandingOneDimKernel_zero_le (a k L : ℝ) (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) :
    expandingOneDimKernel a k L 0 ≤ 1 := by
  have hz : expandingOneDimKernel a k L 0 = (L ^ (a / 6))⁻¹ := by
    simp [expandingOneDimKernel, expandingOneDimWeight,
      Real.zero_rpow (by linarith : k / 6 ≠ 0)]
  rw [hz]
  exact inv_le_one_of_one_le₀ (Real.one_le_rpow hL (show 0 ≤ a / 6 by linarith))

theorem expandingOneDimKernel_antitone (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) :
    AntitoneOn (expandingOneDimKernel a k L) (Ici 0) := by
  intro x hx y hy hxy
  change 0 ≤ x at hx
  change 0 ≤ y at hy
  unfold expandingOneDimKernel
  apply (inv_le_inv₀ (expandingOneDimWeight_pos a k L y hL)
    (expandingOneDimWeight_pos a k L x hL)).mpr
  unfold expandingOneDimWeight
  simp only [abs_of_nonneg hx, abs_of_nonneg hy]
  gcongr
  linarith

/-- Below the scale, the inverse weight is controlled by the locally integrable power. -/
theorem expandingOneDimKernel_le_low (a k L x : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hL : 1 ≤ L) (hx : 0 < x) :
    expandingOneDimKernel a k L x ≤ L ^ (-a / 6) * x ^ (a / 6 - 1) := by
  have hpow : x ^ (1 - a / 6) ≤ (1 + x ^ 2) ^ ((6 - a) / 12) := by
    calc
      _ = (x ^ 2) ^ ((6 - a) / 12) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
        congr 1
        ring
      _ ≤ _ := Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
  have hden : L ^ (a / 6) * x ^ (1 - a / 6) ≤ expandingOneDimWeight a k L x := by
    unfold expandingOneDimWeight
    exact (mul_le_mul_of_nonneg_left hpow (by positivity)).trans (le_add_of_nonneg_right (by positivity))
  calc
    expandingOneDimKernel a k L x ≤ (L ^ (a / 6) * x ^ (1 - a / 6))⁻¹ :=
      (inv_le_inv₀ (expandingOneDimWeight_pos a k L x hL) (by positivity)).mpr hden
    _ = L ^ (-a / 6) * x ^ (a / 6 - 1) := by
      rw [mul_inv_rev, ← Real.rpow_neg (by linarith : 0 ≤ L), ← Real.rpow_neg hx.le]
      have h₁ : -(a / 6) = -a / 6 := by ring
      have h₂ : -(1 - a / 6) = a / 6 - 1 := by ring
      rw [h₁, h₂]
      ring

/-- Above the scale, the inverse weight has an integrable high-order tail. -/
theorem expandingOneDimKernel_le_high (a k L x : ℝ) (hL : 1 ≤ L) (hx : 0 < x) :
    expandingOneDimKernel a k L x ≤ L ^ (k / 6 - 1) * x ^ (-k / 6) := by
  have hden : L ^ (1 - k / 6) * x ^ (k / 6) ≤ expandingOneDimWeight a k L x := by
    unfold expandingOneDimWeight
    rw [abs_of_pos hx]
    exact le_add_of_nonneg_left (by positivity)
  calc
    expandingOneDimKernel a k L x ≤ (L ^ (1 - k / 6) * x ^ (k / 6))⁻¹ :=
      (inv_le_inv₀ (expandingOneDimWeight_pos a k L x hL) (by positivity)).mpr hden
    _ = L ^ (k / 6 - 1) * x ^ (-k / 6) := by
      rw [mul_inv_rev, ← Real.rpow_neg (by linarith : 0 ≤ L), ← Real.rpow_neg hx.le]
      have h₁ : -(1 - k / 6) = k / 6 - 1 := by ring
      have h₂ : -(k / 6) = -k / 6 := by ring
      rw [h₁, h₂]
      ring

/-- The normalized weight is exactly the manuscript's volume-weighted Fourier density. -/
theorem expandingSobolevWeightSq_original (a k L : ℝ) (hL : 1 ≤ L) (n : frequencyLattice) :
    (2 * Real.pi * L) ^ 12 *
        ((L ^ (-2 : ℝ) + (‖n‖ / L) ^ 2) ^ (6 - a) + (‖n‖ / L) ^ (2 * k)) =
      (2 * Real.pi) ^ 12 * expandingSobolevWeightSq a k L n := by
  have hLp : 0 < L := by linarith
  have hbase : L ^ (-2 : ℝ) + (‖n‖ / L) ^ 2 =
      L ^ (-2 : ℝ) * (1 + ‖n‖ ^ 2) := by
    rw [Real.rpow_neg hLp.le, Real.rpow_two]
    field_simp
  have hlow : L ^ 12 * (L ^ (-2 : ℝ)) ^ (6 - a) = L ^ (2 * a) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hLp.le, ← Real.rpow_add hLp]
    congr 1
    ring
  have hhigh : L ^ 12 / L ^ (2 * k) = L ^ (12 - 2 * k) := by
    rw [← Real.rpow_natCast, Real.rpow_sub hLp]
    norm_num
  rw [hbase, Real.mul_rpow (by positivity) (by positivity),
    Real.div_rpow (norm_nonneg n) hLp.le, mul_pow]
  unfold expandingSobolevWeightSq
  calc
    _ = (2 * Real.pi) ^ 12 *
        ((L ^ 12 * (L ^ (-2 : ℝ)) ^ (6 - a)) * (1 + ‖n‖ ^ 2) ^ (6 - a) +
          (L ^ 12 / L ^ (2 * k)) * ‖n‖ ^ (2 * k)) := by ring
    _ = _ := by rw [hlow, hhigh]

end DefocusingNLS

end OAI
