import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingFreeStep

namespace OAI

/-! # The two exact energy components on an expanding torus

The normalized Fourier space has a fixed Hilbert norm.  These two bounded
observations recover the low and high terms of the radius-dependent norm.
-/

open scoped ENNReal

namespace DefocusingNLS

noncomputable def expandingLowFraction (a k L : ℝ) (n : frequencyLattice) : ℝ :=
  L ^ (2 * a) * (1 + ‖n‖ ^ 2) ^ (6 - a) / expandingSobolevWeightSq a k L n

theorem expandingLowFraction_bounds (a k L : ℝ) (hL : 1 ≤ L)
    (n : frequencyLattice) : 0 ≤ expandingLowFraction a k L n ∧
      expandingLowFraction a k L n ≤ 1 := by
  constructor
  · exact div_nonneg (by positivity) (expandingSobolevWeightSq_pos a k L hL n).le
  · apply (div_le_one (expandingSobolevWeightSq_pos a k L hL n)).mpr
    unfold expandingSobolevWeightSq
    exact le_add_of_nonneg_right (by positivity)

theorem expandingHighFraction_eq (a k L : ℝ) (hL : 1 ≤ L)
    (n : frequencyLattice) :
    1 - expandingLowFraction a k L n =
      L ^ (12 - 2 * k) * ‖n‖ ^ (2 * k) / expandingSobolevWeightSq a k L n := by
  have hp := (expandingSobolevWeightSq_pos a k L hL n).ne'
  unfold expandingLowFraction
  field_simp
  unfold expandingSobolevWeightSq
  ring

noncomputable def fourierEnergyComponent (w : frequencyLattice → ℝ)
    (hw : ∀ n, 0 ≤ w n ∧ w n ≤ 1) : FourierL2 →L[ℂ] FourierL2 :=
  let F : FourierL2 → FourierL2 := fun f =>
    ⟨fun n => (Real.sqrt (w n) : ℂ) * f n, by
      apply (lp.memℓp f).mono'
      intro n
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)]
      exact mul_le_of_le_one_left (norm_nonneg _) (Real.sqrt_le_one.mpr (hw n).2)⟩
  LinearMap.mkContinuous
    { toFun := F
      map_add' := by intro f g; ext n; exact mul_add _ _ _
      map_smul' := by intro c f; ext n; change _ * (c * _) = c * (_ * _); ring }
    1 (by
      intro f
      rw [one_mul]
      apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      intro n
      change ‖(Real.sqrt (w n) : ℂ) * f n‖ ≤ ‖f n‖
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)]
      exact mul_le_of_le_one_left (norm_nonneg _) (Real.sqrt_le_one.mpr (hw n).2))

@[simp] theorem fourierEnergyComponent_apply (w : frequencyLattice → ℝ)
    (hw : ∀ n, 0 ≤ w n ∧ w n ≤ 1) (f : FourierL2) (n : frequencyLattice) :
    fourierEnergyComponent w hw f n = (Real.sqrt (w n) : ℂ) * f n := rfl

theorem fourierEnergyComponent_norm_sq (w : frequencyLattice → ℝ)
    (hw : ∀ n, 0 ≤ w n ∧ w n ≤ 1) (f : FourierL2) :
    ‖fourierEnergyComponent w hw f‖ ^ 2 = ∑' n, w n * ‖f n‖ ^ 2 := by
  have he := lp.norm_rpow_eq_tsum (p := 2) (by norm_num)
    (fourierEnergyComponent w hw f)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at he
  rw [he]
  apply tsum_congr
  intro n
  rw [fourierEnergyComponent_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (hw n).1]

theorem summable_fourierEnergyComponent (w : frequencyLattice → ℝ)
    (hw : ∀ n, 0 ≤ w n ∧ w n ≤ 1) (f : FourierL2) :
    Summable (fun n => w n * ‖f n‖ ^ 2) := by
  have h := lp.hasSum_norm (p := 2) (by norm_num) (fourierEnergyComponent w hw f)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  convert h.summable using 1
  funext n
  rw [fourierEnergyComponent_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (hw n).1]

noncomputable def expandingLowEnergy (a k L : ℝ) (hL : 1 ≤ L) :
    FourierL2 →L[ℂ] FourierL2 :=
  fourierEnergyComponent (expandingLowFraction a k L) (expandingLowFraction_bounds a k L hL)

noncomputable def expandingHighEnergy (a k L : ℝ) (hL : 1 ≤ L) :
    FourierL2 →L[ℂ] FourierL2 :=
  fourierEnergyComponent (fun n => 1 - expandingLowFraction a k L n)
    (fun n => ⟨sub_nonneg.mpr (expandingLowFraction_bounds a k L hL n).2,
      sub_le_self _ (expandingLowFraction_bounds a k L hL n).1⟩)

theorem expandingEnergy_norm_sq (a k L : ℝ) (hL : 1 ≤ L) (f : FourierL2) :
    ‖f‖ ^ 2 = ‖expandingLowEnergy a k L hL f‖ ^ 2 +
      ‖expandingHighEnergy a k L hL f‖ ^ 2 := by
  have hl := summable_fourierEnergyComponent (expandingLowFraction a k L)
    (expandingLowFraction_bounds a k L hL) f
  have hh := summable_fourierEnergyComponent (fun n => 1 - expandingLowFraction a k L n)
    (fun n => ⟨sub_nonneg.mpr (expandingLowFraction_bounds a k L hL n).2,
      sub_le_self _ (expandingLowFraction_bounds a k L hL n).1⟩) f
  rw [expandingLowEnergy, expandingHighEnergy, fourierEnergyComponent_norm_sq,
    fourierEnergyComponent_norm_sq, ← hl.tsum_add hh]
  have he := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) f
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at he
  rw [he]
  apply tsum_congr
  intro n
  ring

end DefocusingNLS

end OAI
