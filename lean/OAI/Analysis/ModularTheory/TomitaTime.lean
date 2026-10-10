import OAI.Analysis.ModularTheory.TomitaLp
import OAI.Analysis.OperatorAlgebra.LpFourierIntegralAE

namespace OAI

/-! Time-domain realizations of the regularized Tomita vectors, and the
identification of their weighted transforms in the actual L² representation. -/

noncomputable section
open MeasureTheory FourierTransform

namespace WeakPureInfiniteness
open BoundedRecovery

lemma modularTomitaKernel_continuous (n : ℕ) : Continuous (modularTomitaKernel n) := by
  unfold modularTomitaKernel weightedGaussianKernel
  fun_prop

lemma modularTomitaKernel_bounded (n : ℕ) : ∃ C : ℝ, ∀ t, ‖modularTomitaKernel n t‖ ≤ C := by
  let a : ℝ := (n + 1 : ℝ) / 4
  let C : ℂ := (((Real.pi : ℂ) / (a : ℂ)) ^ (1 / 2 : ℂ))⁻¹ * Complex.exp (a / 4 : ℂ)
  refine ⟨‖C‖, fun t => ?_⟩
  change ‖C * Complex.exp (-(a : ℂ) * t ^ 2 + Complex.I * a * t)‖ ≤ ‖C‖
  have he : -(a : ℂ) * t ^ 2 + Complex.I * a * t =
      ((-a * t ^ 2 : ℝ) : ℂ) + Complex.I * ((a * t : ℝ) : ℂ) := by
    push_cast
    ring
  rw [norm_mul, he, Complex.norm_exp]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_im, zero_mul, one_mul, sub_self, add_zero]
  exact mul_le_of_le_one_right (norm_nonneg _) (Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by dsimp only [a]; positivity))
      (sq_nonneg t)))

lemma modularTomitaKernel_memLp (n : ℕ) :
    MemLp (modularTomitaKernel n) 2 (volume : Measure ℝ) := by
  obtain ⟨C, hC⟩ := modularTomitaKernel_bounded n
  apply (memLp_two_iff_integrable_sq_norm
    (modularTomitaKernel_continuous n).aestronglyMeasurable).mpr
  apply ((modularTomitaKernel_integrable n).norm.const_mul C).mono'
    ((modularTomitaKernel_continuous n).norm.pow 2).aestronglyMeasurable
  exact ae_of_all _ (fun t => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), pow_two]
    exact mul_le_mul_of_nonneg_right (hC t) (norm_nonneg _))

def modularTomitaKernelVector (n : ℕ) : Lp ℂ 2 (volume : Measure ℝ) :=
  (modularTomitaKernel_memLp n).toLp (modularTomitaKernel n)

lemma modularTomitaKernelVector_ae (n : ℕ) :
    modularTomitaKernelVector n =ᵐ[volume] modularTomitaKernel n := MemLp.coeFn_toLp _

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma modularTomitaTimeFunction_memLp (D : RealSpectralCalculus H) (n : ℕ) (x : H) :
    MemLp (fun t => modularTomitaKernel n t • D.unitary (-t) x) 2
      (volume : Measure ℝ) := by
  apply (modularTomitaKernel_memLp n).of_le_mul (c := ‖x‖)
    (((modularTomitaKernel_continuous n).smul
      ((D.continuous_unitary_apply x).comp continuous_neg)).aestronglyMeasurable)
  exact ae_of_all _ (fun t => by
    change ‖modularTomitaKernel n t • D.unitary (-t) x‖ ≤ _
    rw [norm_smul, D.norm_unitary_apply, mul_comm])

def modularTomitaTimeVector (D : RealSpectralCalculus H) (n : ℕ) (x : H) :
    Lp H 2 (volume : Measure ℝ) :=
  (modularTomitaTimeFunction_memLp D n x).toLp
    (fun t => modularTomitaKernel n t • D.unitary (-t) x)

lemma modularTomitaTimeVector_ae (D : RealSpectralCalculus H) (n : ℕ) (x : H) :
    modularTomitaTimeVector D n x =ᵐ[volume]
      (fun t => modularTomitaKernel n t • D.unitary (-t) x) := MemLp.coeFn_toLp _

lemma modularTomitaTimeVector_fourier (D : RealSpectralCalculus H)
    {x y : H} (hxy : (x, y) ∈ D.halfGraph)
    (g : BoundedContinuousFunction ℝ ℂ)
    (hg : Integrable (fun ω : ℝ => ‖g ω‖ ^ 2 * Real.exp (2 * Real.pi * ω))) (n : ℕ) :
    vectorLpRepresentation volume g (𝓕 (modularTomitaTimeVector D n x)) =
      modularTomitaFourierVector D hxy g hg n := by
  apply Lp.ext
  filter_upwards [vectorLpMultiplier_ae volume g (𝓕 (modularTomitaTimeVector D n x)),
    fourier_toLp_ae_of_integrable _
      (integrable_spectral_orbit D _ (modularTomitaKernel_integrable n) x)
      (modularTomitaTimeFunction_memLp D n x), modularTomitaFourierVector_ae D hxy g hg n]
    with ω hg' hF hV
  change (vectorLpMultiplier volume g (𝓕 (modularTomitaTimeVector D n x))) ω = _
  change (𝓕 (modularTomitaTimeVector D n x) : Lp H 2 (volume : Measure ℝ)) ω = _ at hF
  rw [hg', hF, hV]
  rfl

lemma modularCoefficient_kernelVector (S : StandardModularData H)
    (a : H →L[ℂ] H) (n : ℕ) :
    modularLpRepresentation volume S.D a
      (modularScalarInclusion volume S (modularTomitaKernelVector n)) =
        modularTomitaTimeVector S.D n (a S.xi) := by
  apply Lp.ext
  filter_upwards [modularLpRepresentation_ae volume S.D a
    (modularScalarInclusion volume S (modularTomitaKernelVector n)),
    modularScalarInclusion_ae volume S (modularTomitaKernelVector n),
    modularTomitaKernelVector_ae n, modularTomitaTimeVector_ae S.D n (a S.xi)]
    with t ha hs hk ht
  rw [ha, hs, hk, ht, map_smul, S.fixes_xi, map_smul, map_smul]

end WeakPureInfiniteness

end

end OAI
