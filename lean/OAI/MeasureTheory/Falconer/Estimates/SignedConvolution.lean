import OAI.MeasureTheory.Falconer.Fourier.MeasureKernelConvolution

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Filter

 theorem signed_difference_balance (τ σ : Measure ℝ)
    [IsFiniteMeasure τ] [IsFiniteMeasure σ] :
    τ + (τ.toSignedMeasure-σ.toSignedMeasure).toJordanDecomposition.negPart =
    σ + (τ.toSignedMeasure-σ.toSignedMeasure).toJordanDecomposition.posPart := by
  apply Measure.toSignedMeasure_eq_toSignedMeasure_iff.mp
  rw [Measure.toSignedMeasure_add, Measure.toSignedMeasure_add]
  have h := SignedMeasure.toSignedMeasure_toJordanDecomposition
    (τ.toSignedMeasure-σ.toSignedMeasure)
  unfold JordanDecomposition.toSignedMeasure at h
  exact (sub_eq_sub_iff_add_eq_add.mp h).symm.trans (add_comm _ _)

 theorem kernelMeasureConvolution_sub_jordan (K : ℝ → ℂ)
    (hK : Continuous K) (hi : Integrable K) (τ σ : Measure ℝ)
    [IsFiniteMeasure τ] [IsFiniteMeasure σ] :
    (fun x => kernelMeasureConvolution K τ x-kernelMeasureConvolution K σ x) =ᵐ[volume]
    (fun x => kernelMeasureConvolution K
      (τ.toSignedMeasure-σ.toSignedMeasure).toJordanDecomposition.posPart x -
      kernelMeasureConvolution K
      (τ.toSignedMeasure-σ.toSignedMeasure).toJordanDecomposition.negPart x) := by
  let P := (τ.toSignedMeasure-σ.toSignedMeasure).toJordanDecomposition.posPart
  let N := (τ.toSignedMeasure-σ.toSignedMeasure).toJordanDecomposition.negPart
  have hτ := (kernelMeasureConvolution_prod_integrable K hK hi τ).prod_right_ae
  have hσ := (kernelMeasureConvolution_prod_integrable K hK hi σ).prod_right_ae
  have hP := (kernelMeasureConvolution_prod_integrable K hK hi P).prod_right_ae
  have hN := (kernelMeasureConvolution_prod_integrable K hK hi N).prod_right_ae
  filter_upwards [hτ,hσ,hP,hN] with x hxτ hxσ hxP hxN
  have he := congrArg (fun μ : Measure ℝ => ∫ y, K (x-y) ∂μ)
    (signed_difference_balance τ σ)
  rw [integral_add_measure hxτ hxN, integral_add_measure hxσ hxP] at he
  exact sub_eq_sub_iff_add_eq_add.mpr (he.trans (add_comm _ _))

 theorem kernelMeasureConvolution_sub_L1 (K : ℝ → ℂ)
    (hK : Continuous K) (hi : Integrable K) (τ σ : Measure ℝ)
    [IsFiniteMeasure τ] [IsFiniteMeasure σ] :
    Integrable (fun x => kernelMeasureConvolution K τ x-kernelMeasureConvolution K σ x) ∧
    (∫ x, ‖kernelMeasureConvolution K τ x-kernelMeasureConvolution K σ x‖) ≤
      (τ.toSignedMeasure-σ.toSignedMeasure).totalVariation.real univ * ∫ x, ‖K x‖ := by
  let P := (τ.toSignedMeasure-σ.toSignedMeasure).toJordanDecomposition.posPart
  let N := (τ.toSignedMeasure-σ.toSignedMeasure).toJordanDecomposition.negPart
  obtain ⟨hP,bP⟩ := kernelMeasureConvolution_L1 K hK hi P
  obtain ⟨hN,bN⟩ := kernelMeasureConvolution_L1 K hK hi N
  have he := kernelMeasureConvolution_sub_jordan K hK hi τ σ
  refine ⟨(hP.sub hN).congr he.symm, ?_⟩
  calc
    _ = ∫ x, ‖kernelMeasureConvolution K P x-kernelMeasureConvolution K N x‖ :=
      integral_congr_ae (he.mono (fun x hx => congrArg norm hx))
    _ ≤ ∫ x, ‖kernelMeasureConvolution K P x‖+‖kernelMeasureConvolution K N x‖ :=
      integral_mono (hP.sub hN).norm (hP.norm.add hN.norm) (fun x => norm_sub_le _ _)
    _ = (∫ x, ‖kernelMeasureConvolution K P x‖)+(∫ x, ‖kernelMeasureConvolution K N x‖) :=
      integral_add hP.norm hN.norm
    _ ≤ P.real univ * (∫ x, ‖K x‖)+N.real univ * (∫ x, ‖K x‖) := add_le_add bP bN
    _ = _ := by rw [← add_mul, SignedMeasure.totalVariation, measureReal_add_apply]

 theorem shellKernelMeasureConvolution_sub_L1 (τ σ : Measure ℝ)
    [IsFiniteMeasure τ] [IsFiniteMeasure σ] (n : ℕ) :
    Integrable (fun x => kernelMeasureConvolution (sourceShellKernel n) τ x-
      kernelMeasureConvolution (sourceShellKernel n) σ x) ∧
    (∫ x, ‖kernelMeasureConvolution (sourceShellKernel n) τ x-
      kernelMeasureConvolution (sourceShellKernel n) σ x‖) ≤
      (τ.toSignedMeasure-σ.toSignedMeasure).totalVariation.real univ *
      ∫ x, ‖sourceShellKernel 0 x‖ := by
  simpa only [sourceShellKernel_uniform_L1] using kernelMeasureConvolution_sub_L1
    (sourceShellKernel n) (sourceShellKernel_continuous n) (sourceShellKernel_integrable n) τ σ

end PlanarFalconer

end OAI
