import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCircularLeadingBound
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFieldParameterLimit

namespace OAI

/-! A uniform perturbation estimate for the full circular spectral field. -/

namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem circularFullField_free_difference_bound
    (νp νm μp μm η : ℂ) (m : ℕ) (hm : 1 ≤ m) (q : ℂ) (ε : ℝ)
    (hq : ‖spectralDiagonalCoefficient m q‖+‖spectralCrossCoefficient m q‖ ≤ ε)
    (t T : ℝ) (ht : t ≤ T) (X Y : E₄) :
    let δ := circularExponentDifference νp νm μp μm+ε
    ‖(circularLeadingField t X+circularBoundedField νp νm η m q X)-
      (circularLeadingField t Y+circularBoundedField μp μm η 1 0 Y)‖ ≤
      (Real.exp (2*T)/2+circularFieldBound μp μm η 1 0+δ)*‖X-Y‖+δ*‖Y‖ := by
  let δ := circularExponentDifference νp νm μp μm+ε
  have hε : 0 ≤ ε := (add_nonneg (norm_nonneg _) (norm_nonneg _)).trans hq
  have hδ : 0 ≤ δ := add_nonneg (circularExponentDifference_nonneg _ _ _ _) hε
  have hlead : ‖circularLeadingField t (X-Y)‖ ≤ (Real.exp (2*T)/2)*‖X-Y‖ :=
    (circularLeadingField_norm t (X-Y)).trans
      (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right
        (Real.exp_le_exp.mpr (by linarith)) (by norm_num)) (norm_nonneg _))
  have hfree := circularBoundedField_norm μp μm η 1 (by omega) 0 0 (by simp) (X-Y)
  have herr := circularBoundedField_free_bound νp νm μp μm η m hm q ε hq X
  have he : (circularLeadingField t X+circularBoundedField νp νm η m q X)-
      (circularLeadingField t Y+circularBoundedField μp μm η 1 0 Y) =
      (circularLeadingField t (X-Y)+circularBoundedField μp μm η 1 0 (X-Y))+
        (circularBoundedField νp νm η m q X-circularBoundedField μp μm η 1 0 X) := by
    rw [circularLeadingField_sub,circularBoundedField_sub]
    abel
  rw [he]
  calc
    _ ≤ (‖circularLeadingField t (X-Y)‖+‖circularBoundedField μp μm η 1 0 (X-Y)‖)+
        ‖circularBoundedField νp νm η m q X-circularBoundedField μp μm η 1 0 X‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
    _ ≤ ((Real.exp (2*T)/2)*‖X-Y‖+circularFieldBound μp μm η 1 0*‖X-Y‖)+δ*‖X‖ :=
      add_le_add (add_le_add hlead hfree) herr
    _ ≤ ((Real.exp (2*T)/2)*‖X-Y‖+circularFieldBound μp μm η 1 0*‖X-Y‖)+
        δ*(‖X-Y‖+‖Y‖) := by gcongr; exact norm_le_norm_sub_add X Y
    _ = _ := by ring

end DefocusingNLS

end OAI
