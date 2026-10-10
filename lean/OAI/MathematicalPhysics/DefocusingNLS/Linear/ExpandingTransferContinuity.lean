import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingWeightContinuity

namespace OAI

/-! # Operator-norm continuity of the weight identification

Only the positive weight identification is continuous in operator norm.
The free Schrödinger group continues to be used with strong continuity.
-/

open Filter Topology
open scoped ENNReal

namespace DefocusingNLS

/-- A frequency-independent modulus bounds the diagonal identification operators. -/
theorem expandingScaleTransfer_from_one_sub_norm_le (a k L M : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (hM : 1 ≤ M) :
    ‖expandingScaleTransfer a k 1 L ha hk le_rfl hL -
      expandingScaleTransfer a k 1 M ha hk le_rfl hM‖ ≤
      |L ^ a - M ^ a| + |L ^ (6 - k) - M ^ (6 - k)| := by
  let D := |L ^ a - M ^ a| + |L ^ (6 - k) - M ^ (6 - k)|
  have hD : 0 ≤ D := by dsimp [D]; positivity
  apply ContinuousLinearMap.opNorm_le_bound _ hD
  intro f
  calc
    _ ≤ ‖D • f‖ := by
      apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      intro n
      change ‖(expandingScaleRatio a k 1 L n : ℂ) * f n -
          (expandingScaleRatio a k 1 M n : ℂ) * f n‖ ≤ ‖D • f n‖
      rw [← sub_mul, ← Complex.ofReal_sub, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, norm_smul, Real.norm_eq_abs, abs_of_nonneg hD]
      exact mul_le_mul_of_nonneg_right
        (expandingScaleRatio_difference_le a k L M hL hM n) (norm_nonneg _)
    _ = D * ‖f‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hD]

/-- Positive-weight identification with `Y_1` is operator-norm continuous in `L`. -/
theorem continuous_expandingScaleTransfer_from_one (a k : ℝ) (ha : 0 < a) (hk : 8 < k) :
    Continuous (fun L : {L : ℝ // 1 ≤ L} =>
      expandingScaleTransfer a k 1 L.1 ha hk le_rfl L.2) := by
  have hlo : Continuous (fun L : {L : ℝ // 1 ≤ L} => L.1 ^ a) :=
    continuous_subtype_val.rpow_const (fun L => Or.inl (by linarith [L.2] : L.1 ≠ 0))
  have hhi : Continuous (fun L : {L : ℝ // 1 ≤ L} => L.1 ^ (6 - k)) :=
    continuous_subtype_val.rpow_const (fun L => Or.inl (by linarith [L.2] : L.1 ≠ 0))
  rw [continuous_iff_continuousAt]
  intro L₀
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hd : Tendsto (fun L : {L : ℝ // 1 ≤ L} =>
      |L.1 ^ a - L₀.1 ^ a| + |L.1 ^ (6 - k) - L₀.1 ^ (6 - k)|) (𝓝 L₀) (𝓝 0) := by
    have hc : Continuous (fun L : {L : ℝ // 1 ≤ L} =>
        |L.1 ^ a - L₀.1 ^ a| + |L.1 ^ (6 - k) - L₀.1 ^ (6 - k)|) :=
      ((hlo.sub continuous_const).abs).add ((hhi.sub continuous_const).abs)
    simpa only [sub_self, abs_zero, zero_add] using (hc.continuousAt (x := L₀)).tendsto
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun L => expandingScaleTransfer_from_one_sub_norm_le a k L.1 L₀.1 ha hk L.2 L₀.2) hd

end DefocusingNLS

end OAI
