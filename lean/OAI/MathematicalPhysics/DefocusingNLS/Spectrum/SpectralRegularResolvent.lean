import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRegularSource
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.NormedSpace

namespace OAI

/-! Resolving the regular two-channel equation on a fixed finite radial interval. -/

open scoped BoundedContinuousFunction
namespace DefocusingNLS

noncomputable def spectralRegularPairKernel (d : ℕ) (R α : ℝ)
    (hR : 0 ≤ R) (hα : 0 < α) : RegularSpectralSpace →L[ℂ] RegularSpectralSpace :=
  (spectralRegularKernelCLM d 1 R α hR hα).prodMap
    (spectralRegularKernelCLM d (-1) R α hR hα)

theorem spectralRegularPairKernel_norm (d : ℕ) (R α : ℝ)
    (hR : 0 ≤ R) (hα : 0 < α) :
    ‖spectralRegularPairKernel d R α hR hα‖ ≤ 1/(2*α) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  rw [one_div_mul_eq_div]
  apply max_le
  · exact (spectralRegularWeightedKernel_norm d 1 R α hR hα v.1).trans
      (div_le_div_of_nonneg_right (norm_fst_le v) (by positivity))
  · exact (spectralRegularWeightedKernel_norm d (-1) R α hR hα v.2).trans
      (div_le_div_of_nonneg_right (norm_snd_le v) (by positivity))

theorem spectralRegular_isUnit (d : ℕ) (R α : ℝ) (hR : 0 ≤ R) (hα : 0 < α)
    (A B : ℝ →ᵇ ℂ) (cp cm : ℂ)
    (hgap : spectralRegularSourceBound A B cp cm < 2*α) :
    IsUnit (1-spectralRegularPairKernel d R α hR hα*spectralRegularSourceCLM A B cp cm) := by
  have hn : ‖spectralRegularPairKernel d R α hR hα*spectralRegularSourceCLM A B cp cm‖<1 := by
    calc
      _ ≤ ‖spectralRegularPairKernel d R α hR hα‖*‖spectralRegularSourceCLM A B cp cm‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (1/(2*α))*spectralRegularSourceBound A B cp cm :=
        mul_le_mul (spectralRegularPairKernel_norm d R α hR hα)
          (spectralRegularSourceCLM_norm A B cp cm) (norm_nonneg _) (by positivity)
      _ < 1 := by rw [one_div_mul_eq_div]; exact (div_lt_one (by positivity)).mpr hgap
  convert! isUnit_one_sub_of_norm_lt_one
    (R := RegularSpectralSpace →L[ℂ] RegularSpectralSpace)
    (x := spectralRegularPairKernel d R α hR hα*spectralRegularSourceCLM A B cp cm)
    (by convert! hn)

noncomputable def spectralRegularResolvent (d : ℕ) (R α : ℝ) (hR : 0 ≤ R) (hα : 0 < α)
    (A B : ℝ →ᵇ ℂ) (cp cm lam : ℂ) : RegularSpectralSpace →L[ℂ] RegularSpectralSpace :=
  Ring.inverse (1-spectralRegularPairKernel d R α hR hα*
    spectralRegularSourceCLM A B (cp+Complex.I*lam) (cm-Complex.I*lam))

theorem spectralRegularResolvent_solve (d : ℕ) (R α : ℝ) (hR : 0 ≤ R) (hα : 0 < α)
    (A B : ℝ →ᵇ ℂ) (cp cm lam : ℂ)
    (hgap : spectralRegularSourceBound A B (cp+Complex.I*lam) (cm-Complex.I*lam)<2*α)
    (g : RegularSpectralSpace) :
    let v := spectralRegularResolvent d R α hR hα A B cp cm lam g
    v=g+spectralRegularPairKernel d R α hR hα
      (spectralRegularSourceCLM A B (cp+Complex.I*lam) (cm-Complex.I*lam) v) := by
  intro v
  have hu := spectralRegular_isUnit d R α hR hα A B _ _ hgap
  have he := congrArg (fun T : RegularSpectralSpace →L[ℂ] RegularSpectralSpace => T g)
    (Ring.mul_inverse_cancel _ hu)
  change v-spectralRegularPairKernel d R α hR hα
    (spectralRegularSourceCLM A B (cp+Complex.I*lam) (cm-Complex.I*lam) v)=g at he
  exact sub_eq_iff_eq_add.mp he

local instance : IsBoundedSMul ℂ (RegularSpectralSpace →L[ℂ] RegularSpectralSpace) := by
  convert! (NormedSpace.toIsBoundedSMul (𝕜 := ℂ)
    (E := RegularSpectralSpace →L[ℂ] RegularSpectralSpace))

theorem spectralRegularResolvent_analyticAt (d : ℕ) (R α : ℝ)
    (hR : 0 ≤ R) (hα : 0 < α) (A B : ℝ →ᵇ ℂ) (cp cm z : ℂ)
    (hgap : spectralRegularSourceBound A B (cp+Complex.I*z) (cm-Complex.I*z)<2*α) :
    AnalyticAt ℂ (spectralRegularResolvent d R α hR hα A B cp cm) z := by
  let D := fun lam => 1-spectralRegularPairKernel d R α hR hα*
    spectralRegularSourceCLM A B (cp+Complex.I*lam) (cm-Complex.I*lam)
  have hp : AnalyticAt ℂ (fun lam => spectralRegularPairKernel d R α hR hα*
      spectralRegularSourceCLM A B (cp+Complex.I*lam) (cm-Complex.I*lam)) z := by
    convert! (AnalyticAt.mul (𝕜 := ℂ) (A := RegularSpectralSpace →L[ℂ] RegularSpectralSpace)
      (z := z) (f := fun _ : ℂ => spectralRegularPairKernel d R α hR hα)
      (g := fun lam => spectralRegularSourceCLM A B (cp+Complex.I*lam) (cm-Complex.I*lam))
      analyticAt_const (spectralRegularSourceCLM_analyticAt A B cp cm z))
  have hD : AnalyticAt ℂ D z := by
    convert! (analyticAt_const (v := (1 : RegularSpectralSpace →L[ℂ] RegularSpectralSpace))).sub hp
  have hu : IsUnit (D z) := spectralRegular_isUnit d R α hR hα A B _ _ hgap
  have hi : AnalyticAt ℂ Ring.inverse (D z) := by
    have hi := analyticAt_inverse (𝕜 := ℂ) (A := RegularSpectralSpace →L[ℂ] RegularSpectralSpace)
      (by convert! hu.unit)
    convert! hi using 1
  exact hi.comp hD

end DefocusingNLS

end OAI
