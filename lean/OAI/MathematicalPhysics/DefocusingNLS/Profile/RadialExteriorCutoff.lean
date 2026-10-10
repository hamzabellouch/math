import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialOddPowerBound
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialTruncatedNonlinearity

namespace OAI

/-! A global Lipschitz extension which agrees with the exterior polynomial near its limiting value. -/

open Set
namespace DefocusingNLS

noncomputable def radialComplexClamp (m : ℂ) (δ : ℝ) (z : ℂ) : ℂ :=
  m + (radialAmplitudeClamp (-δ) δ (z-m).re : ℂ) +
    Complex.I*(radialAmplitudeClamp (-δ) δ (z-m).im : ℂ)

theorem radialComplexClamp_continuous (m : ℂ) (δ : ℝ) :
    Continuous (radialComplexClamp m δ) := by
  unfold radialComplexClamp radialAmplitudeClamp
  fun_prop

theorem radialComplexClamp_eq (m : ℂ) (δ : ℝ) (z : ℂ) (hz : ‖z-m‖ ≤ δ) :
    radialComplexClamp m δ z=z := by
  have hr := (abs_le.mp ((Complex.abs_re_le_norm (z-m)).trans hz))
  have hi := (abs_le.mp ((Complex.abs_im_le_norm (z-m)).trans hz))
  rw [radialComplexClamp,radialAmplitudeClamp_eq _ _ _ hr,
    radialAmplitudeClamp_eq _ _ _ hi]
  have hparts := Complex.re_add_im (z-m)
  linear_combination hparts

theorem radialComplexClamp_bound (m : ℂ) (δ : ℝ) (hδ : 0 ≤ δ) (z : ℂ) :
    ‖radialComplexClamp m δ z‖ ≤ ‖m‖+2*δ := by
  have hcl (x : ℝ) : ‖radialAmplitudeClamp (-δ) δ x‖ ≤ δ := by
    rw [Real.norm_eq_abs,abs_le]
    exact radialAmplitudeClamp_mem _ _ _ (by linarith)
  unfold radialComplexClamp
  calc
    _ ≤ ‖m+(radialAmplitudeClamp (-δ) δ (z-m).re : ℂ)‖+
        ‖Complex.I*(radialAmplitudeClamp (-δ) δ (z-m).im : ℂ)‖ := norm_add_le _ _
    _ ≤ (‖m‖+‖(radialAmplitudeClamp (-δ) δ (z-m).re : ℂ)‖)+
        ‖Complex.I*(radialAmplitudeClamp (-δ) δ (z-m).im : ℂ)‖ :=
      add_le_add (norm_add_le _ _) le_rfl
    _ ≤ ‖m‖+2*δ := by
      rw [norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Complex.norm_real]
      linarith [hcl (z-m).re,hcl (z-m).im]

theorem radialComplexClamp_difference (m : ℂ) (δ : ℝ) (z w : ℂ) :
    ‖radialComplexClamp m δ z-radialComplexClamp m δ w‖ ≤ 2*‖z-w‖ := by
  have hcl (x y : ℝ) :
      ‖radialAmplitudeClamp (-δ) δ x-radialAmplitudeClamp (-δ) δ y‖ ≤ ‖x-y‖ := by
    simpa only [dist_eq_norm,NNReal.coe_one,one_mul] using
      (radialAmplitudeClamp_lipschitz (-δ) δ).dist_le_mul x y
  have he : radialComplexClamp m δ z-radialComplexClamp m δ w =
      ((radialAmplitudeClamp (-δ) δ (z-m).re-
        radialAmplitudeClamp (-δ) δ (w-m).re : ℝ) : ℂ)+
      Complex.I*((radialAmplitudeClamp (-δ) δ (z-m).im-
        radialAmplitudeClamp (-δ) δ (w-m).im : ℝ) : ℂ) := by
    unfold radialComplexClamp
    push_cast
    ring
  rw [he]
  calc
    _ ≤ ‖((radialAmplitudeClamp (-δ) δ (z-m).re-
        radialAmplitudeClamp (-δ) δ (w-m).re : ℝ) : ℂ)‖+
      ‖Complex.I*((radialAmplitudeClamp (-δ) δ (z-m).im-
        radialAmplitudeClamp (-δ) δ (w-m).im : ℝ) : ℂ)‖ := norm_add_le _ _
    _ ≤ ‖(z-m).re-(w-m).re‖+‖(z-m).im-(w-m).im‖ := by
      rw [norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Complex.norm_real]
      exact add_le_add (hcl _ _) (hcl _ _)
    _ ≤ 2*‖z-w‖ := by
      have hr := Complex.abs_re_le_norm (z-w)
      have hi := Complex.abs_im_le_norm (z-w)
      simp only [Complex.sub_re,Complex.sub_im,sub_sub_sub_cancel_right,Real.norm_eq_abs]
      simpa only [two_mul,Complex.sub_re,Complex.sub_im] using! add_le_add hr hi

noncomputable def radialExteriorCutoffPower (n : ℕ) (m : ℂ) (δ : ℝ) (z : ℂ) : ℂ :=
  oddPowerNonlinearity n (radialComplexClamp m δ z)

theorem radialExteriorCutoffPower_continuous (n : ℕ) (m : ℂ) (δ : ℝ) :
    Continuous (radialExteriorCutoffPower n m δ) :=
  (contDiff_oddPowerNonlinearity n).continuous.comp (radialComplexClamp_continuous m δ)

theorem radialExteriorCutoffPower_eq (n : ℕ) (m : ℂ) (δ : ℝ) (z : ℂ)
    (hz : ‖z-m‖ ≤ δ) :
    radialExteriorCutoffPower n m δ z=oddPowerNonlinearity n z := by
  rw [radialExteriorCutoffPower,radialComplexClamp_eq m δ z hz]

theorem radialExteriorCutoffPower_difference (n : ℕ) (m : ℂ) (δ : ℝ) (hδ : 0 ≤ δ)
    (z w : ℂ) :
    ‖radialExteriorCutoffPower n m δ z-radialExteriorCutoffPower n m δ w‖ ≤
      (2*(2*(n : ℝ)+1)*(‖m‖+2*δ)^(2*n))*‖z-w‖ := by
  have hp := radial_oddPower_difference n (‖m‖+2*δ) (by positivity)
    (radialComplexClamp m δ z) (radialComplexClamp m δ w)
    (radialComplexClamp_bound m δ hδ z) (radialComplexClamp_bound m δ hδ w)
  calc
    _ ≤ (2*(n : ℝ)+1)*(‖m‖+2*δ)^(2*n)*
        ‖radialComplexClamp m δ z-radialComplexClamp m δ w‖ := hp
    _ ≤ (2*(n : ℝ)+1)*(‖m‖+2*δ)^(2*n)*(2*‖z-w‖) := by
      gcongr
      exact radialComplexClamp_difference m δ z w
    _ = _ := by ring

end DefocusingNLS

end OAI
