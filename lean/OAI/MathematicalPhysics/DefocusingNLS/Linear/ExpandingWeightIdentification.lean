import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingTransferContinuity
import Mathlib.Analysis.Normed.Ring.Units

namespace OAI

/-! # The two-sided identification between exact expanding Sobolev spaces

The radius-one weight identifies every `Y_L`, `L ≥ 1`, with the same Hilbert
space.  Both this identification and its inverse depend continuously on `L`.
-/

open Filter Topology
open scoped ENNReal

namespace DefocusingNLS

/-- The inverse identification loses at most the explicit high-frequency scale factor. -/
theorem expandingSobolevWeight_one_le (a k L : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (n : frequencyLattice) :
    expandingSobolevWeight a k 1 n ≤ L ^ (k - 6) * expandingSobolevWeight a k L n := by
  have hLp : 0 < L := by linarith
  have hcancel : L ^ (2 * k - 12) * L ^ (12 - 2 * k) = 1 := by
    rw [← Real.rpow_add hLp,
      show (2 * k - 12) + (12 - 2 * k) = 0 by ring, Real.rpow_zero]
  have hlo : 1 ≤ L ^ (2 * k - 12) * L ^ (2 * a) := by
    rw [← Real.rpow_add hLp]
    exact Real.one_le_rpow hL (by linarith)
  have hsq : expandingSobolevWeightSq a k 1 n ≤
      L ^ (2 * k - 12) * expandingSobolevWeightSq a k L n := by
    unfold expandingSobolevWeightSq
    simp only [Real.one_rpow, one_mul]
    rw [mul_add, ← mul_assoc, ← mul_assoc, hcancel, one_mul]
    exact add_le_add (le_mul_of_one_le_left (by positivity) hlo) le_rfl
  have hp : (L ^ (k - 6)) ^ 2 = L ^ (2 * k - 12) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hLp.le]
    congr 1
    ring
  have hsqrt := Real.sqrt_le_sqrt hsq
  rw [← hp, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (Real.rpow_nonneg hLp.le _)] at hsqrt
  unfold expandingSobolevWeight
  nlinarith [mul_le_mul_of_nonneg_left hsqrt
    (show 0 ≤ (2 * Real.pi) ^ 6 by positivity)]

noncomputable def expandingInverseRatio (a k L : ℝ) (n : frequencyLattice) : ℝ :=
  expandingSobolevWeight a k 1 n / expandingSobolevWeight a k L n

theorem expandingInverseRatio_nonneg (a k L : ℝ) (hL : 1 ≤ L) (n : frequencyLattice) :
    0 ≤ expandingInverseRatio a k L n := by
  exact (div_pos (expandingSobolevWeight_pos a k 1 le_rfl n)
    (expandingSobolevWeight_pos a k L hL n)).le

theorem expandingInverseRatio_le (a k L : ℝ) (ha : 0 < a) (hk : 8 < k)
    (hL : 1 ≤ L) (n : frequencyLattice) : expandingInverseRatio a k L n ≤ L ^ (k - 6) := by
  apply (div_le_iff₀ (expandingSobolevWeight_pos a k L hL n)).2
  exact expandingSobolevWeight_one_le a k L ha hk hL n

noncomputable def expandingInverseVector (a k L : ℝ) (ha : 0 < a) (hk : 8 < k)
    (hL : 1 ≤ L) (f : FourierL2) : FourierL2 :=
  ⟨fun n => (expandingInverseRatio a k L n : ℂ) * f n, by
    apply (lp.memℓp ((L ^ (k - 6) : ℝ) • f)).mono'
    intro n
    simp only [lp.coeFn_smul, Pi.smul_apply, norm_smul, Real.norm_eq_abs, norm_mul,
      Complex.norm_real, abs_of_nonneg (expandingInverseRatio_nonneg a k L hL n)]
    exact mul_le_mul_of_nonneg_right ((expandingInverseRatio_le a k L ha hk hL n).trans
      (le_abs_self _)) (norm_nonneg _)⟩

theorem expandingInverseVector_norm_le (a k L : ℝ) (ha : 0 < a) (hk : 8 < k)
    (hL : 1 ≤ L) (f : FourierL2) :
    ‖expandingInverseVector a k L ha hk hL f‖ ≤ L ^ (k - 6) * ‖f‖ := by
  calc
    _ ≤ ‖(L ^ (k - 6) : ℝ) • f‖ := by
      apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      intro n
      change ‖(expandingInverseRatio a k L n : ℂ) * f n‖ ≤ ‖(L ^ (k - 6) : ℝ) • f n‖
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (expandingInverseRatio_nonneg a k L hL n), norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right ((expandingInverseRatio_le a k L ha hk hL n).trans
        (le_abs_self _)) (norm_nonneg _)
    _ = _ := by rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ L) _)]

noncomputable def expandingInverseTransfer (a k L : ℝ) (ha : 0 < a) (hk : 8 < k)
    (hL : 1 ≤ L) : FourierL2 →L[ℂ] FourierL2 :=
  LinearMap.mkContinuous
    { toFun := expandingInverseVector a k L ha hk hL
      map_add' := by
        intro f g
        ext n
        change (expandingInverseRatio a k L n : ℂ) * (f n + g n) = _
        simp only [mul_add]
        rfl
      map_smul' := by
        intro c f
        ext n
        change (expandingInverseRatio a k L n : ℂ) * (c * f n) =
          c * ((expandingInverseRatio a k L n : ℂ) * f n)
        ring }
    (L ^ (k - 6)) (expandingInverseVector_norm_le a k L ha hk hL)

/-- Two-sided inverse of the canonical radius-one identification. -/
noncomputable def expandingWeightUnit (a k L : ℝ) (ha : 0 < a) (hk : 8 < k)
    (hL : 1 ≤ L) : (FourierL2 →L[ℂ] FourierL2)ˣ where
  val := expandingScaleTransfer a k 1 L ha hk le_rfl hL
  inv := expandingInverseTransfer a k L ha hk hL
  val_inv := by
    ext f n
    change (expandingScaleRatio a k 1 L n : ℂ) *
      ((expandingInverseRatio a k L n : ℂ) * f n) = f n
    unfold expandingScaleRatio expandingInverseRatio
    push_cast
    have h1 := (Complex.ofReal_ne_zero.mpr (expandingSobolevWeight_pos a k 1 le_rfl n).ne')
    have hL' := (Complex.ofReal_ne_zero.mpr (expandingSobolevWeight_pos a k L hL n).ne')
    field_simp
  inv_val := by
    ext f n
    change (expandingInverseRatio a k L n : ℂ) *
      ((expandingScaleRatio a k 1 L n : ℂ) * f n) = f n
    unfold expandingScaleRatio expandingInverseRatio
    push_cast
    have h1 := (Complex.ofReal_ne_zero.mpr (expandingSobolevWeight_pos a k 1 le_rfl n).ne')
    have hL' := (Complex.ofReal_ne_zero.mpr (expandingSobolevWeight_pos a k L hL n).ne')
    field_simp

theorem continuous_expandingInverseTransfer (a k : ℝ) (ha : 0 < a) (hk : 8 < k) :
    Continuous (fun L : {L : ℝ // 1 ≤ L} => expandingInverseTransfer a k L.1 ha hk L.2) := by
  have heq (L : {L : ℝ // 1 ≤ L}) :
      Ring.inverse (expandingScaleTransfer a k 1 L.1 ha hk le_rfl L.2) =
        expandingInverseTransfer a k L.1 ha hk L.2 :=
    Ring.inverse_unit (expandingWeightUnit a k L.1 ha hk L.2)
  have hc : Continuous (fun L : {L : ℝ // 1 ≤ L} =>
      Ring.inverse (expandingScaleTransfer a k 1 L.1 ha hk le_rfl L.2)) := by
    rw [continuous_iff_continuousAt]
    intro L
    have hi : ContinuousAt (Ring.inverse : (FourierL2 →L[ℂ] FourierL2) →
        (FourierL2 →L[ℂ] FourierL2))
        (expandingScaleTransfer a k 1 L.1 ha hk le_rfl L.2) :=
      NormedRing.inverse_continuousAt (expandingWeightUnit a k L.1 ha hk L.2)
    exact hi.comp ((continuous_expandingScaleTransfer_from_one a k ha hk).continuousAt (x := L))
  simpa only [heq] using hc

end DefocusingNLS

end OAI
