import Mathlib
import OAI.MeasureTheory.Falconer.Fourier.KernelFourierIdentity
import OAI.MeasureTheory.Falconer.Fourier.MeasureKernelConvolution
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Shells.ShellFrequencyEnergy
import OAI.MeasureTheory.Falconer.Shells.ShellKernels
import OAI.MeasureTheory.Falconer.Shells.Shells
import OAI.MeasureTheory.Falconer.Shells.SmoothShellPartition
import OAI.MeasureTheory.FalconerCompletion.Fourier.SignedVariationFinite

namespace OAI

/-! Angular cutoffs and derivative estimates. -/

open _root_.OAI.PlanarFalconer

section
section
namespace CurrentFalconer.MonotoneShell
open MeasureTheory Set Filter PlanarFalconer
open scoped Topology ENNReal FourierTransform
lemma inverse_add (f g : ℝ → ℂ) (hf : Integrable f) (hg : Integrable g) :
    sourceInverseKernel (f+g) = sourceInverseKernel f+sourceInverseKernel g := by
  have he : 𝓕 (f+g) = 𝓕 f+𝓕 g :=
    VectorFourier.fourierIntegral_add Real.continuous_fourierChar (innerSL ℝ).continuous₂ hf hg
  funext x
  simp only [sourceInverseKernel,he,Pi.add_apply,smul_add]
lemma inverse_smul (c : ℂ) (f : ℝ → ℂ) :
    sourceInverseKernel (c • f) = c • sourceInverseKernel f := by
  have he : 𝓕 (c • f) = c • 𝓕 f :=
    VectorFourier.fourierIntegral_const_smul Real.fourierChar volume (innerₗ ℝ) f c
  funext x
  simp only [sourceInverseKernel,he,Pi.smul_apply]
  exact smul_comm _ _ _
lemma inverse_sub (f g : ℝ → ℂ) (hf : Integrable f) (hg : Integrable g) :
    sourceInverseKernel (f-g) = sourceInverseKernel f-sourceInverseKernel g := by
  have he : f-g = f+(-1:ℂ) • g := by simp [sub_eq_add_neg]
  rw [he,inverse_add _ _ hf (hg.smul _),inverse_smul]
  simp [sub_eq_add_neg]
noncomputable def complexMultiplier (ν : ComplexMeasure ℝ) (n : ℕ) (r : ℝ) : ℂ :=
  (sourceShellBand n r : ℂ)*complexChar ν r
lemma complexMultiplier_continuous (ν : ComplexMeasure ℝ) (n : ℕ) : Continuous (complexMultiplier ν n) :=
  (Complex.continuous_ofReal.comp (sourceShellBand_smooth n).continuous).mul (complexChar_continuous ν)
lemma complexMultiplier_zero (ν : ComplexMeasure ℝ) (n : ℕ) (r : ℝ)
    (hr : r ∉ dyadicShell (n+1)) : complexMultiplier ν n r = 0 := by
  have he : sourceShellBand n r = 0 := by
    by_contra hn
    exact hr (sourceShellBand_support n hn)
  simp [complexMultiplier,he]
lemma complexMultiplier_memLp (ν : ComplexMeasure ℝ) (n : ℕ) (p : ℝ≥0∞) :
    MemLp (complexMultiplier ν n) p volume :=
  (complexMultiplier_continuous ν n).memLp_of_hasCompactSupport
    (HasCompactSupport.intro (dyadicShell_compact (n+1)) (complexMultiplier_zero ν n))
lemma complexMultiplier_decompose (ν : ComplexMeasure ℝ) (n : ℕ) :
    complexMultiplier ν n =
      (sourceShellMultiplier (ComplexMeasure.re ν).toJordanDecomposition.posPart n -
       sourceShellMultiplier (ComplexMeasure.re ν).toJordanDecomposition.negPart n) +
      Complex.I • (sourceShellMultiplier (ComplexMeasure.im ν).toJordanDecomposition.posPart n -
       sourceShellMultiplier (ComplexMeasure.im ν).toJordanDecomposition.negPart n) := by
  funext r
  simp only [complexMultiplier,complexChar,signedChar,sourceShellMultiplier,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  ring
lemma complexMultiplier_positive (μ : FiniteMeasure ℝ) (n : ℕ) :
    complexMultiplier (complexOfPositive μ) n = sourceShellMultiplier (μ : Measure ℝ) n := by
  funext r
  simp [complexMultiplier,sourceShellMultiplier,complexChar_positive]
lemma complexMultiplier_sub (μ ν : ComplexMeasure ℝ) [IsFiniteMeasure μ.variation] [IsFiniteMeasure ν.variation]
    (n : ℕ) : complexMultiplier (μ-ν) n = complexMultiplier μ n-complexMultiplier ν n := by
  funext r
  simp [complexMultiplier,complexChar_sub,mul_sub]
end CurrentFalconer.MonotoneShell
end
end

section
section
namespace CurrentFalconer.MonotoneShell
open MeasureTheory Set Filter PlanarFalconer
open scoped Topology ENNReal
noncomputable def signedConv (s : SignedMeasure ℝ) (n : ℕ) (x : ℝ) : ℂ :=
  kernelMeasureConvolution (sourceShellKernel n) s.toJordanDecomposition.posPart x -
  kernelMeasureConvolution (sourceShellKernel n) s.toJordanDecomposition.negPart x
noncomputable def complexConv (ν : ComplexMeasure ℝ) (n : ℕ) (x : ℝ) : ℂ :=
  signedConv (ComplexMeasure.re ν) n x+Complex.I*signedConv (ComplexMeasure.im ν) n x
lemma signedConv_L1 (s : SignedMeasure ℝ) (n : ℕ) : Integrable (signedConv s n) ∧
    (∫ x, ‖signedConv s n x‖) ≤ s.variation.real univ * ∫ x, ‖sourceShellKernel 0 x‖ := by
  have hp := shellKernelMeasureConvolution_L1 s.toJordanDecomposition.posPart n
  have hn := shellKernelMeasureConvolution_L1 s.toJordanDecomposition.negPart n
  refine ⟨hp.1.sub hn.1,?_⟩
  calc
    _ ≤ ∫ x, ‖kernelMeasureConvolution (sourceShellKernel n) s.toJordanDecomposition.posPart x‖ +
        ‖kernelMeasureConvolution (sourceShellKernel n) s.toJordanDecomposition.negPart x‖ :=
      integral_mono (hp.1.sub hn.1).norm (hp.1.norm.add hn.1.norm) (fun x => norm_sub_le _ _)
    _ = _ := integral_add hp.1.norm hn.1.norm
    _ ≤ s.toJordanDecomposition.posPart.real univ * (∫ x, ‖sourceShellKernel 0 x‖) +
        s.toJordanDecomposition.negPart.real univ * (∫ x, ‖sourceShellKernel 0 x‖) := add_le_add hp.2 hn.2
    _ = _ := by rw [←s.totalVariation_eq_variation,SignedMeasure.totalVariation,measureReal_add_apply,add_mul]
lemma complexConv_integrable (ν : ComplexMeasure ℝ) (n : ℕ) : Integrable (complexConv ν n) :=
  (signedConv_L1 _ n).1.add ((signedConv_L1 _ n).1.const_mul Complex.I)
lemma complexConv_L1_bound (ν : ComplexMeasure ℝ) [IsFiniteMeasure ν.variation] (n : ℕ) :
    (∫ x, ‖complexConv ν n x‖) ≤ (2*ν.variation.real univ) * ∫ x, ‖sourceShellKernel 0 x‖ := by
  have hr := signedConv_L1 (ComplexMeasure.re ν) n
  have hi := signedConv_L1 (ComplexMeasure.im ν) n
  have hrv : (ComplexMeasure.re ν).variation.real univ ≤ ν.variation.real univ :=
    ENNReal.toReal_mono (measure_ne_top _ _) (real_variation_le ν univ)
  have hiv : (ComplexMeasure.im ν).variation.real univ ≤ ν.variation.real univ :=
    ENNReal.toReal_mono (measure_ne_top _ _) (imag_variation_le ν univ)
  calc
    _ ≤ ∫ x, ‖signedConv (ComplexMeasure.re ν) n x‖ +
        ‖Complex.I*signedConv (ComplexMeasure.im ν) n x‖ :=
      integral_mono (complexConv_integrable ν n).norm
        (hr.1.norm.add (hi.1.const_mul Complex.I).norm) (fun x => norm_add_le _ _)
    _ = (∫ x, ‖signedConv (ComplexMeasure.re ν) n x‖) +
        (∫ x, ‖signedConv (ComplexMeasure.im ν) n x‖) := by
      rw [integral_add hr.1.norm (hi.1.const_mul Complex.I).norm]
      simp only [norm_mul,Complex.norm_I,one_mul]
    _ ≤ ((ComplexMeasure.re ν).variation.real univ+(ComplexMeasure.im ν).variation.real univ) *
        (∫ x, ‖sourceShellKernel 0 x‖) := by
      rw [add_mul]
      exact add_le_add hr.2 hi.2
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (integral_nonneg (fun x => norm_nonneg _))
lemma complexConv_inverse (ν : ComplexMeasure ℝ) (n : ℕ) :
    complexConv ν n = sourceInverseKernel (complexMultiplier ν n) := by
  have hi (μ : Measure ℝ) [IsFiniteMeasure μ] : Integrable (sourceShellMultiplier μ n) :=
    memLp_one_iff_integrable.mp (sourceShellMultiplier_memLp μ n 1)
  rw [complexMultiplier_decompose,inverse_add _ _ ((hi _).sub (hi _)) (((hi _).sub (hi _)).smul Complex.I),
    inverse_smul,inverse_sub _ _ (hi _) (hi _),inverse_sub _ _ (hi _) (hi _)]
  funext x
  simp only [complexConv,signedConv,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,
    shellKernelMeasureConvolution_fourier]
lemma complexConv_positive (μ : FiniteMeasure ℝ) (n : ℕ) :
    complexConv (complexOfPositive μ) n = kernelMeasureConvolution (sourceShellKernel n) (μ : Measure ℝ) := by
  rw [complexConv_inverse,complexMultiplier_positive]
  funext x
  exact (shellKernelMeasureConvolution_fourier μ n x).symm
lemma complexConv_sub (μ ν : ComplexMeasure ℝ) [IsFiniteMeasure μ.variation] [IsFiniteMeasure ν.variation]
    (n : ℕ) : complexConv (μ-ν) n = complexConv μ n-complexConv ν n := by
  simp only [complexConv_inverse,complexMultiplier_sub]
  exact inverse_sub _ _ (memLp_one_iff_integrable.mp (complexMultiplier_memLp μ n 1))
    (memLp_one_iff_integrable.mp (complexMultiplier_memLp ν n 1))

end CurrentFalconer.MonotoneShell
end
end

end OAI
