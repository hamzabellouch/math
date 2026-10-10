import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRegularAnalytic

namespace OAI

/-! Parameter derivatives of the constructed regular columns. The derivative
source is obtained from the resolvent equation, rather than postulated. -/

open Filter Topology
open scoped BoundedContinuousFunction
namespace DefocusingNLS

noncomputable def spectralRegularSourceSlope : RegularSpectralSpace →L[ℂ] RegularSpectralSpace :=
  ((-Complex.I) • ContinuousLinearMap.fst ℂ (ℝ →ᵇ ℂ) (ℝ →ᵇ ℂ)).prod
    (Complex.I • ContinuousLinearMap.snd ℂ (ℝ →ᵇ ℂ) (ℝ →ᵇ ℂ))

theorem spectralRegularSourceCLM_affine (A B : ℝ →ᵇ ℂ) (cp cm lam : ℂ) :
    spectralRegularSourceCLM A B (cp + Complex.I * lam) (cm - Complex.I * lam) =
      spectralRegularSourceCLM A B cp cm + lam • spectralRegularSourceSlope := by
  apply ContinuousLinearMap.ext
  intro v
  apply Prod.ext <;> apply BoundedContinuousFunction.ext <;> intro r
  all_goals
    simp only [spectralRegularSourceCLM, spectralRegularSourceValue,
      spectralRegularSourceSlope, add_apply, smul_apply,
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', LinearMap.mkContinuous_apply,
      LinearMap.coe_mk, AddHom.coe_mk, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, BoundedContinuousFunction.add_apply,
      BoundedContinuousFunction.sub_apply, BoundedContinuousFunction.mul_apply,
      BoundedContinuousFunction.smul_apply, smul_eq_mul]
    ring

theorem spectralRegularSourceCLM_hasDerivAt (A B : ℝ →ᵇ ℂ) (cp cm z : ℂ) :
    HasDerivAt (fun lam => spectralRegularSourceCLM A B
      (cp + Complex.I * lam) (cm - Complex.I * lam)) spectralRegularSourceSlope z := by
  simp_rw [spectralRegularSourceCLM_affine]
  have h := ((hasDerivAt_id z).smul_const spectralRegularSourceSlope).const_add
    (spectralRegularSourceCLM A B cp cm)
  simp only [one_smul, id_eq] at h
  convert! h using 1

theorem spectralRegularSolutionSource_deriv (d : ℕ) (R α : ℝ)
    (hR : 0 ≤ R) (hα : 0 < α) (A B : ℝ →ᵇ ℂ) (cp cm : ℂ)
    (c : ℂ × ℂ) (z : ℂ)
    (hgap : spectralRegularSourceBound A B (cp + Complex.I * z) (cm - Complex.I * z) < 2 * α) :
    deriv (spectralRegularSolutionSource d R α hR hα A B cp cm c) z =
      spectralRegularSourceCLM A B (cp + Complex.I * z) (cm - Complex.I * z)
        (deriv (spectralRegularVector d R α hR hα A B cp cm c) z) +
      spectralRegularSourceSlope (spectralRegularVector d R α hR hα A B cp cm c z) := by
  have hv := (spectralRegularVector_analyticAt d R α hR hα A B cp cm c z hgap).differentiableAt.hasDerivAt
  have hh := (spectralRegularSourceCLM_hasDerivAt A B cp cm z).clm_apply hv
  convert! hh.deriv.trans (add_comm _ _) using 1

theorem spectralRegularVector_deriv_equation (d : ℕ) (R α : ℝ)
    (hR : 0 ≤ R) (hα : 0 < α) (A B : ℝ →ᵇ ℂ) (cp cm : ℂ)
    (c : ℂ × ℂ) (z : ℂ)
    (hgap : spectralRegularSourceBound A B (cp + Complex.I * z) (cm - Complex.I * z) < 2 * α) :
    deriv (spectralRegularVector d R α hR hα A B cp cm c) z =
      spectralRegularPairKernel d R α hR hα
        (deriv (spectralRegularSolutionSource d R α hR hα A B cp cm c) z) := by
  have hv := (spectralRegularVector_analyticAt d R α hR hα A B cp cm c z hgap).differentiableAt.hasDerivAt
  have hs := (spectralRegularSolutionSource_analyticAt d R α hR hα A B cp cm c z hgap).differentiableAt.hasDerivAt
  have hg : Continuous (fun lam : ℂ => spectralRegularSourceBound A B
      (cp + Complex.I * lam) (cm - Complex.I * lam)) := by
    unfold spectralRegularSourceBound
    fun_prop
  have he : spectralRegularVector d R α hR hα A B cp cm c =ᶠ[𝓝 z]
      fun lam => spectralRegularInitial R α hα.le c + spectralRegularPairKernel d R α hR hα
        (spectralRegularSolutionSource d R α hR hα A B cp cm c lam) := by
    filter_upwards [hg.continuousAt.eventually (gt_mem_nhds hgap)] with lam hlam
    exact spectralRegularVector_equation d R α hR hα A B cp cm c lam hlam
  have hh := ((spectralRegularPairKernel d R α hR hα).hasFDerivAt.comp_hasDerivAt z hs).const_add
    (spectralRegularInitial R α hα.le c)
  exact hv.unique (hh.congr_of_eventuallyEq he)

end DefocusingNLS

end OAI
