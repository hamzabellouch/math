import OAI.Analysis.CircleDomains.Sobolev.ComplexPolarDifferential
import OAI.Analysis.CircleDomains.Sobolev.PolarAnnulusIntegral
import OAI.Analysis.CircleDomains.Topology.RoundCircleParametrization

namespace OAI

/-! The angular edge of a polar rectangle is the actual circle line
integral, with the normalization and orientation fixed explicitly. -/
open Set Function MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma pulledPolarForm_periodic (P Q : ℂ → ℝ) (R : ℝ) :
    Periodic (fun θ => pulledPlanarForm P Q (fun p => Complex.polarCoord.symm p) (0,1) (R,θ))
      (2*Real.pi) := by
  intro θ
  simp only [pulledPlanarForm,complexPolarSymm_fderiv]
  simp only [Complex.polarCoord_symm_apply,Real.cos_add_two_pi,Real.sin_add_two_pi]

lemma pulledPolarForm_radius_zero (P Q : ℂ → ℝ) (θ : ℝ) :
    pulledPlanarForm P Q (fun p => Complex.polarCoord.symm p) (0,1) (0,θ) = 0 := by
  simp only [pulledPlanarForm,complexPolarSymm_fderiv]
  simp

lemma planarFormIntegral_circle_eq_polar (P Q : ℂ → ℝ) (R : ℝ) :
    planarFormIntegral P Q (unitCircleParam 0 R) =
      ∫ θ in (-Real.pi)..Real.pi,
        pulledPlanarForm P Q (fun p => Complex.polarCoord.symm p) (0,1) (R,θ) := by
  let B : ℝ → ℝ := fun θ =>
    pulledPlanarForm P Q (fun p => Complex.polarCoord.symm p) (0,1) (R,θ)
  have he : planarFormIntegral P Q (unitCircleParam 0 R) =
      ∫ t in (0 : ℝ)..1, (2*Real.pi) * B (2*Real.pi*t) := by
    unfold planarFormIntegral
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [(unitCircleParam_hasDerivAt R t).deriv]
    dsimp only [B,pulledPlanarForm]
    rw [complexPolarSymm_fderiv,complex_polar_symm_circleMap]
    dsimp only [unitCircleParam]
    simp only [Complex.mul_re,Complex.mul_im,Complex.add_re,
      Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
      circleMap_zero_re,circleMap_zero_im]
    rw [show (2 : ℂ).re = 2 from rfl,show (2 : ℂ).im = 0 from rfl]
    ring
  rw [he]
  have hn : (∫ t in (0 : ℝ)..1, (2*Real.pi) * B (2*Real.pi*t)) =
      ∫ θ in (0 : ℝ)..2*Real.pi, B θ := by
    rw [intervalIntegral.integral_const_mul]
    simpa only [smul_eq_mul,mul_zero,mul_one] using
      (intervalIntegral.smul_integral_comp_mul_left B (a := (0 : ℝ)) (b := 1) (2*Real.pi))
  rw [hn]
  have hp := (pulledPolarForm_periodic P Q R).intervalIntegral_add_eq (-Real.pi) 0
  have hbound : -Real.pi+2*Real.pi = Real.pi := by ring
  simpa only [hbound,zero_add] using hp.symm

end CircleDomainRigidity

end

end OAI
