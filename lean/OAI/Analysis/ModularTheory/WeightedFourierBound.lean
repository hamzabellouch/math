import OAI.Analysis.ModularTheory.WeightedFourierLimit

namespace OAI

/-! The integrable bound for the actual regularized Tomita orbit. This is
the dominated-convergence step at compact spectral vectors; the bound comes
from the half-graph equation, not from an unbounded exponential multiplier. -/

noncomputable section
open MeasureTheory Filter FourierTransform
open scoped Topology

namespace WeakPureInfiniteness
open BoundedRecovery

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma modularShiftedHalfGaussian_norm (D : RealSpectralCalculus H)
    {x y : H} (hxy : (x, y) ∈ D.halfGraph) (s : ℝ) (n : ℕ) :
    ‖D.calculus (modularShiftedHalfGaussian n s) x‖ ≤ ‖y‖ := by
  rw [modularShiftedHalfGaussian_halfGraph D hxy]
  have hb : ‖modularGaussian n‖ ≤ 1 :=
    (BoundedContinuousFunction.norm_le zero_le_one).mpr (modularGaussian_norm_le n)
  exact ((D.shift s).norm_calculus_apply_le (modularGaussian n) y).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hb (norm_nonneg y))

lemma modularTomitaKernel_fourier_norm (D : RealSpectralCalculus H)
    {x y : H} (hxy : (x, y) ∈ D.halfGraph)
    (χ : BoundedContinuousFunction ℝ ℂ) (hχ : HasCompactSupport (χ : ℝ → ℂ))
    (n : ℕ) (ω : ℝ) :
    ‖𝓕 (fun t => modularTomitaKernel n t • D.unitary (-t) (D.calculus χ x)) ω‖ ≤
      Real.exp (Real.pi * ω) * ‖D.calculus χ y‖ := by
  rw [fourier_spectral_orbit D _ (modularTomitaKernel_integrable n) χ hχ x ω,
    modularTomitaKernel_calculus D n _ χ hχ x, norm_smul]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have he : (2 * Real.pi * ω) / 2 = Real.pi * ω := by ring
  rw [he]
  exact mul_le_mul_of_nonneg_left
    (modularShiftedHalfGaussian_norm D (D.halfGraph_calculus hxy χ) _ n)
    (Real.exp_pos _).le

lemma modularTomitaKernel_fourier_continuous (D : RealSpectralCalculus H)
    (n : ℕ) (x : H) :
    Continuous (𝓕 (fun t => modularTomitaKernel n t • D.unitary (-t) x)) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂
    (integrable_spectral_orbit D _ (modularTomitaKernel_integrable n) x)

lemma modularTomitaKernel_weighted_integral_limit (D : RealSpectralCalculus H)
    {x y : H} (hxy : (x, y) ∈ D.halfGraph)
    (χ : BoundedContinuousFunction ℝ ℂ) (hχ : HasCompactSupport (χ : ℝ → ℂ))
    (g : BoundedContinuousFunction ℝ ℂ)
    (hg : Integrable (fun ω : ℝ => ‖g ω‖ ^ 2 * Real.exp (2 * Real.pi * ω))) :
    Tendsto (fun n => ∫ ω : ℝ,
      ‖g ω • (𝓕 (fun t => modularTomitaKernel n t •
        D.unitary (-t) (D.calculus χ x)) ω -
          (Real.exp (Real.pi * ω) : ℂ) • D.calculus χ y)‖ ^ 2)
      atTop (𝓝 0) := by
  let F (n : ℕ) (ω : ℝ) :=
    𝓕 (fun t => modularTomitaKernel n t • D.unitary (-t) (D.calculus χ x)) ω
  let L (ω : ℝ) := (Real.exp (Real.pi * ω) : ℂ) • D.calculus χ y
  let E (n : ℕ) (ω : ℝ) := ‖g ω • (F n ω - L ω)‖ ^ 2
  let B (ω : ℝ) := (4 * ‖D.calculus χ y‖ ^ 2) *
    (‖g ω‖ ^ 2 * Real.exp (2 * Real.pi * ω))
  have hL (ω : ℝ) : ‖L ω‖ = Real.exp (Real.pi * ω) * ‖D.calculus χ y‖ := by
    simp only [L, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
  have hb (n : ℕ) (ω : ℝ) : E n ω ≤ B ω := by
    have hF := modularTomitaKernel_fourier_norm D hxy χ hχ n ω
    have hd : ‖F n ω - L ω‖ ≤ 2 *
        (Real.exp (Real.pi * ω) * ‖D.calculus χ y‖) := by
      exact (norm_sub_le _ _).trans (by rw [hL]; dsimp only [F]; linarith)
    have hs := mul_le_mul_of_nonneg_left hd (norm_nonneg (g ω))
    have hsq := pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hs 2
    have he : Real.exp (Real.pi * ω) ^ 2 = Real.exp (2 * Real.pi * ω) := by
      rw [← Real.exp_nat_mul]
      congr 1
      norm_num
      ring
    dsimp only [E, B]
    rw [norm_smul]
    calc
      _ ≤ (‖g ω‖ * (2 * (Real.exp (Real.pi * ω) * ‖D.calculus χ y‖))) ^ 2 := hsq
      _ = _ := by ring_nf; rw [he]; ring_nf
  have hm (n : ℕ) : AEStronglyMeasurable (E n) volume := by
    have hf := modularTomitaKernel_fourier_continuous D n (D.calculus χ x)
    exact (g.continuous.smul (hf.sub (by dsimp only [L]; fun_prop))).norm.pow 2
      |>.aestronglyMeasurable
  have hp (ω : ℝ) : Tendsto (fun n => E n ω) atTop (𝓝 0) := by
    have h := (((modularTomitaKernel_fourier_limit D hxy χ hχ ω).sub_const
      (L ω)).const_smul (g ω)).norm.pow 2
    simpa only [E, F, L, sub_self, smul_zero, norm_zero, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] using h
  have hi : Integrable B := hg.const_mul _
  have h := tendsto_integral_of_dominated_convergence B hm hi
    (fun n => ae_of_all _ (fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hb n ω)) (ae_of_all _ hp)
  simpa only [E, F, L, integral_zero] using h

end WeakPureInfiniteness

end

end OAI
