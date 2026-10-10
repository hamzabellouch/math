import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingFourier

namespace OAI

/-! # Bounded Fourier multipliers in the exact normalized torus space -/

open scoped ENNReal

namespace DefocusingNLS

noncomputable def fourierMultiplierVector (c : ℝ) (hc : 0 ≤ c)
    (w : frequencyLattice → ℂ) (hw : ∀ n, ‖w n‖ ≤ c) (f : FourierL2) : FourierL2 :=
  ⟨fun n => w n * f n, by
    apply (lp.memℓp (c • f)).mono'
    intro n
    simp only [lp.coeFn_smul, Pi.smul_apply, norm_smul, Real.norm_eq_abs,
      norm_mul, abs_of_nonneg hc]
    exact mul_le_mul_of_nonneg_right (hw n) (norm_nonneg _)⟩

theorem fourierMultiplierVector_norm_le (c : ℝ) (hc : 0 ≤ c)
    (w : frequencyLattice → ℂ) (hw : ∀ n, ‖w n‖ ≤ c) (f : FourierL2) :
    ‖fourierMultiplierVector c hc w hw f‖ ≤ c * ‖f‖ := by
  calc
    _ ≤ ‖c • f‖ := by
      apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      intro n
      change ‖w n * f n‖ ≤ ‖c • f n‖
      rw [norm_mul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
      exact mul_le_mul_of_nonneg_right (hw n) (norm_nonneg _)
    _ = _ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]

noncomputable def fourierBoundedMultiplier (c : ℝ) (hc : 0 ≤ c)
    (w : frequencyLattice → ℂ) (hw : ∀ n, ‖w n‖ ≤ c) : FourierL2 →L[ℂ] FourierL2 :=
  LinearMap.mkContinuous
    { toFun := fourierMultiplierVector c hc w hw
      map_add' := by
        intro f g
        ext n
        change w n * (f n + g n) = w n * f n + w n * g n
        ring
      map_smul' := by
        intro z f
        ext n
        change w n * (z * f n) = z * (w n * f n)
        ring }
    c (fourierMultiplierVector_norm_le c hc w hw)

@[simp] theorem fourierBoundedMultiplier_apply (c : ℝ) (hc : 0 ≤ c)
    (w : frequencyLattice → ℂ) (hw : ∀ n, ‖w n‖ ≤ c) (f : FourierL2) (n : frequencyLattice) :
    fourierBoundedMultiplier c hc w hw f n = w n * f n := rfl

theorem fourierBoundedMultiplier_norm_le (c : ℝ) (hc : 0 ≤ c)
    (w : frequencyLattice → ℂ) (hw : ∀ n, ‖w n‖ ≤ c) (f : FourierL2) :
    ‖fourierBoundedMultiplier c hc w hw f‖ ≤ c * ‖f‖ :=
  fourierMultiplierVector_norm_le c hc w hw f

theorem expandingFourierCoefficient_multiplier (a k L c : ℝ) (hc : 0 ≤ c)
    (w : frequencyLattice → ℂ) (hw : ∀ n, ‖w n‖ ≤ c) (f : FourierL2) (n : frequencyLattice) :
    expandingFourierCoefficient a k L (fourierBoundedMultiplier c hc w hw f) n =
      w n * expandingFourierCoefficient a k L f n := by
  simp only [expandingFourierCoefficient, fourierBoundedMultiplier_apply]
  ring

end DefocusingNLS

end OAI
