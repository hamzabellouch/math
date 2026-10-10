import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousYNorm
import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzSobolevLocalization
import Mathlib.Analysis.Normed.Operator.Extend

namespace OAI

/-! # Exact whole-space free evolution in Fourier variables

The similarity factor and dilation are those of (lin:free-flow). The two
homogeneous energies are estimated separately before extending the action to Y.
-/

open MeasureTheory
open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def homogeneousFrequencyEnergy (r : ℝ) (f : E → ℂ) : ℝ :=
  ∫ ξ, ‖ξ‖ ^ (2 * r) * ‖f ξ‖ ^ 2

private theorem frequency_density_dilation (r R : ℝ) (hR : 0 < R)
    (f : E → ℂ) (ξ : E) :
    ‖ξ‖ ^ (2 * r) * ‖f (R • ξ)‖ ^ 2 =
      R ^ (-(2 * r)) * (‖R • ξ‖ ^ (2 * r) * ‖f (R • ξ)‖ ^ 2) := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hR,
    Real.mul_rpow hR.le (norm_nonneg ξ)]
  have hc : R ^ (-(2 * r)) * R ^ (2 * r) = 1 := by
    rw [← Real.rpow_add hR]
    simp
  calc
    _ = 1 * (‖ξ‖ ^ (2 * r) * ‖f (R • ξ)‖ ^ 2) := by ring
    _ = _ := by rw [← hc]; ring

theorem homogeneousFrequencyEnergy_dilation (r R : ℝ) (hR : 0 < R) (f : E → ℂ) :
    homogeneousFrequencyEnergy r (fun ξ => f (R • ξ)) =
      R ^ (-12 - 2 * r) * homogeneousFrequencyEnergy r f := by
  unfold homogeneousFrequencyEnergy
  simp_rw [frequency_density_dilation r R hR f]
  rw [integral_const_mul, Measure.integral_comp_smul_of_nonneg
    (volume : Measure E) (fun ξ => ‖ξ‖ ^ (2 * r) * ‖f ξ‖ ^ 2) R
    (hR := hR.le), finrank_euclideanSpace_fin]
  simp only [smul_eq_mul]
  rw [← mul_assoc]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_neg hR.le, ← Real.rpow_add hR]
  congr 1
  ring

noncomputable def homogeneousFreePhase (s : ℝ) (ξ : E) : ℂ :=
  Complex.exp ((-(Real.exp s - 1) * ‖ξ‖ ^ 2 : ℝ) * Complex.I)

@[simp] theorem homogeneousFreePhase_norm (s : ℝ) (ξ : E) :
    ‖homogeneousFreePhase s ξ‖ = 1 := Complex.norm_exp_ofReal_mul_I _

theorem homogeneousFreePhase_temperate (s : ℝ) :
    (homogeneousFreePhase s).HasTemperateGrowth := by
  have hpoly : (fun ξ : E => -(Real.exp s - 1) * ‖ξ‖ ^ 2).HasTemperateGrowth :=
    (Function.HasTemperateGrowth.const _).mul (Function.hasTemperateGrowth_norm_sq E)
  exact Complex.hasTemperateGrowth_exp_mul_I.comp hpoly

noncomputable def homogeneousFreeAmplitude (a b s : ℝ) : ℂ :=
  Complex.exp ((((6 - a) * s : ℝ) : ℂ) + Complex.I * ((b * s : ℝ) : ℂ))

@[simp] theorem homogeneousFreeAmplitude_norm (a b s : ℝ) :
    ‖homogeneousFreeAmplitude a b s‖ = Real.exp ((6 - a) * s) := by
  simp [homogeneousFreeAmplitude, Complex.norm_exp]

/-- Fourier action of e^((-a+ib)s)[e^(i(1-e^-s)Δ)v](e^(-s/2)y). -/
noncomputable def homogeneousFreeFourier (a b s : ℝ) : 𝓢(E, ℂ) →L[ℂ] 𝓢(E, ℂ) :=
  homogeneousFreeAmplitude a b s •
    (SchwartzMap.smulLeftCLM ℂ (homogeneousFreePhase s)).comp
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        ((Units.mk0 (Real.exp (s / 2)) (Real.exp_ne_zero _)) •
          ContinuousLinearEquiv.refl ℝ E))

@[simp] theorem homogeneousFreeFourier_apply (a b s : ℝ) (ψ : 𝓢(E, ℂ)) (ξ : E) :
    homogeneousFreeFourier a b s ψ ξ =
      homogeneousFreeAmplitude a b s * homogeneousFreePhase s ξ *
        ψ (Real.exp (s / 2) • ξ) := by
  simp only [homogeneousFreeFourier, smul_apply,
    ContinuousLinearMap.comp_apply, SchwartzMap.smulLeftCLM_apply_apply
      (homogeneousFreePhase_temperate s), smul_eq_mul,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
  change homogeneousFreeAmplitude a b s *
    (homogeneousFreePhase s ξ * ψ (Real.exp (s / 2) • ξ)) = _
  ring

/-- Each homogeneous order has its exact similarity exponent. -/
theorem homogeneousFreeFourier_energy (a b s r : ℝ) (ψ : 𝓢(E, ℂ)) :
    homogeneousFrequencyEnergy r (homogeneousFreeFourier a b s ψ) =
      Real.exp ((6 - 2 * a - r) * s) * homogeneousFrequencyEnergy r ψ := by
  have he : homogeneousFrequencyEnergy r (homogeneousFreeFourier a b s ψ) =
      Real.exp ((6 - a) * s) ^ (2 : ℕ) *
        homogeneousFrequencyEnergy r (fun ξ => ψ (Real.exp (s / 2) • ξ)) := by
    unfold homogeneousFrequencyEnergy
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with ξ
    simp only [homogeneousFreeFourier_apply, norm_mul, homogeneousFreeAmplitude_norm,
      homogeneousFreePhase_norm, mul_one, mul_pow]
    ring
  rw [he, homogeneousFrequencyEnergy_dilation r _ (Real.exp_pos _)]
  rw [← Real.exp_nat_mul, ← Real.exp_mul, ← mul_assoc, ← Real.exp_add]
  congr 2
  ring

end DefocusingNLS

end OAI
