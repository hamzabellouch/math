import OAI.Analysis.ModularTheory.TomitaOrbit
import OAI.Analysis.ModularTheory.WeightMonomials

namespace OAI

/-! Weighted L² convergence for the full Tomita orbit. This turns the
frequencywise Gaussian identity into convergence of actual Hilbert-space
vectors, with the square norm required for the core weight calculation. -/

noncomputable section
open MeasureTheory Filter FourierTransform
open scoped Topology

namespace WeakPureInfiniteness
open BoundedRecovery

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma modularTomitaKernel_weighted_integral_limit_all (D : RealSpectralCalculus H)
    {x y : H} (hxy : (x, y) ∈ D.halfGraph)
    (g : BoundedContinuousFunction ℝ ℂ)
    (hg : Integrable (fun ω : ℝ => ‖g ω‖ ^ 2 * Real.exp (2 * Real.pi * ω))) :
    Tendsto (fun n => ∫ ω : ℝ,
      ‖g ω • (𝓕 (fun t => modularTomitaKernel n t •
        D.unitary (-t) x) ω -
          (Real.exp (Real.pi * ω) : ℂ) • y)‖ ^ 2)
      atTop (𝓝 0) := by
  let F (n : ℕ) (ω : ℝ) :=
    𝓕 (fun t => modularTomitaKernel n t • D.unitary (-t) x) ω
  let L (ω : ℝ) := (Real.exp (Real.pi * ω) : ℂ) • y
  let E (n : ℕ) (ω : ℝ) := ‖g ω • (F n ω - L ω)‖ ^ 2
  let B (ω : ℝ) := (4 * ‖y‖ ^ 2) *
    (‖g ω‖ ^ 2 * Real.exp (2 * Real.pi * ω))
  have hL (ω : ℝ) : ‖L ω‖ = Real.exp (Real.pi * ω) * ‖y‖ := by
    simp only [L, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
  have hb (n : ℕ) (ω : ℝ) : E n ω ≤ B ω := by
    have hF := modularTomitaKernel_fourier_norm_all D hxy n ω
    have hd : ‖F n ω - L ω‖ ≤ 2 *
        (Real.exp (Real.pi * ω) * ‖y‖) := by
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
      _ ≤ (‖g ω‖ * (2 * (Real.exp (Real.pi * ω) * ‖y‖))) ^ 2 := hsq
      _ = _ := by ring_nf; rw [he]; ring_nf
  have hm (n : ℕ) : AEStronglyMeasurable (E n) volume := by
    have hf := modularTomitaKernel_fourier_continuous D n x
    exact (g.continuous.smul (hf.sub (by dsimp only [L]; fun_prop))).norm.pow 2
      |>.aestronglyMeasurable
  have hp (ω : ℝ) : Tendsto (fun n => E n ω) atTop (𝓝 0) := by
    have h := (((modularTomitaKernel_fourier_limit_all D hxy ω).sub_const
      (L ω)).const_smul (g ω)).norm.pow 2
    simpa only [E, F, L, sub_self, smul_zero, norm_zero, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] using h
  have hi : Integrable B := hg.const_mul _
  have h := tendsto_integral_of_dominated_convergence B hm hi
    (fun n => ae_of_all _ (fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hb n ω)) (ae_of_all _ hp)
  simpa only [E, F, L, integral_zero] using h


def modularTomitaFourierFunction (D : RealSpectralCalculus H) (n : ℕ)
    (g : BoundedContinuousFunction ℝ ℂ) (x : H) (ω : ℝ) : H :=
  g ω • 𝓕 (fun t => modularTomitaKernel n t • D.unitary (-t) x) ω

lemma modularTomitaFourierFunction_memLp (D : RealSpectralCalculus H)
    {x y : H} (hxy : (x, y) ∈ D.halfGraph) (n : ℕ)
    (g : BoundedContinuousFunction ℝ ℂ)
    (hg : Integrable (fun ω : ℝ => ‖g ω‖ ^ 2 * Real.exp (2 * Real.pi * ω))) :
    MemLp (modularTomitaFourierFunction D n g x) 2 (volume : Measure ℝ) := by
  apply (modularWeightedFunction_memLp g hg).of_le_mul (c := ‖y‖)
    (g.continuous.smul (modularTomitaKernel_fourier_continuous D n x)).aestronglyMeasurable
  exact ae_of_all _ (fun ω => by
    change ‖g ω • 𝓕 (fun t => modularTomitaKernel n t • D.unitary (-t) x) ω‖ ≤ ‖y‖ * ‖g ω * (Real.exp (Real.pi * ω) : ℂ)‖
    rw [norm_smul, norm_mul]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have h := mul_le_mul_of_nonneg_left
      (modularTomitaKernel_fourier_norm_all D hxy n ω) (norm_nonneg (g ω))
    exact h.trans_eq (by ring))

def modularTomitaFourierVector (D : RealSpectralCalculus H)
    {x y : H} (hxy : (x, y) ∈ D.halfGraph)
    (g : BoundedContinuousFunction ℝ ℂ)
    (hg : Integrable (fun ω : ℝ => ‖g ω‖ ^ 2 * Real.exp (2 * Real.pi * ω)))
    (n : ℕ) : Lp H 2 (volume : Measure ℝ) :=
  (modularTomitaFourierFunction_memLp D hxy n g hg).toLp
    (modularTomitaFourierFunction D n g x)

lemma modularTomitaFourierVector_ae (D : RealSpectralCalculus H)
    {x y : H} (hxy : (x, y) ∈ D.halfGraph)
    (g : BoundedContinuousFunction ℝ ℂ)
    (hg : Integrable (fun ω : ℝ => ‖g ω‖ ^ 2 * Real.exp (2 * Real.pi * ω))) (n : ℕ) :
    modularTomitaFourierVector D hxy g hg n =ᵐ[volume]
      modularTomitaFourierFunction D n g x := MemLp.coeFn_toLp _

omit [CompleteSpace H] in
lemma modularTomitaLimitFunction_memLp (g : BoundedContinuousFunction ℝ ℂ)
    (hg : Integrable (fun ω : ℝ => ‖g ω‖ ^ 2 * Real.exp (2 * Real.pi * ω))) (y : H) :
    MemLp (fun ω => modularWeightedFunction g ω • y) 2 (volume : Measure ℝ) := by
  apply (modularWeightedFunction_memLp g hg).of_le_mul (c := ‖y‖)
    (by unfold modularWeightedFunction; fun_prop)
  exact ae_of_all _ (fun ω => by rw [norm_smul, mul_comm])

def modularTomitaLimitVector (g : BoundedContinuousFunction ℝ ℂ)
    (hg : Integrable (fun ω : ℝ => ‖g ω‖ ^ 2 * Real.exp (2 * Real.pi * ω)))
    (y : H) : Lp H 2 (volume : Measure ℝ) :=
  (modularTomitaLimitFunction_memLp g hg y).toLp
    (fun ω => modularWeightedFunction g ω • y)

omit [CompleteSpace H] in
lemma modularTomitaLimitVector_ae (g : BoundedContinuousFunction ℝ ℂ)
    (hg : Integrable (fun ω : ℝ => ‖g ω‖ ^ 2 * Real.exp (2 * Real.pi * ω))) (y : H) :
    modularTomitaLimitVector g hg y =ᵐ[volume]
      (fun ω => modularWeightedFunction g ω • y) := MemLp.coeFn_toLp _

omit [CompleteSpace H] in
lemma modularTomitaLimitVector_norm_sq (g : BoundedContinuousFunction ℝ ℂ)
    (hg : Integrable (fun ω : ℝ => ‖g ω‖ ^ 2 * Real.exp (2 * Real.pi * ω))) (y : H) :
    ‖modularTomitaLimitVector g hg y‖ ^ 2 =
      ‖y‖ ^ 2 * ∫ ω : ℝ, ‖g ω‖ ^ 2 * Real.exp (2 * Real.pi * ω) := by
  rw [vectorLp_norm_sq_integral, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [modularTomitaLimitVector_ae g hg y] with ω hω
  rw [hω, norm_smul, mul_pow, modularWeightedFunction_norm_sq]
  ring

lemma modularTomitaFourierVector_tendsto (D : RealSpectralCalculus H)
    {x y : H} (hxy : (x, y) ∈ D.halfGraph)
    (g : BoundedContinuousFunction ℝ ℂ)
    (hg : Integrable (fun ω : ℝ => ‖g ω‖ ^ 2 * Real.exp (2 * Real.pi * ω))) :
    Tendsto (modularTomitaFourierVector D hxy g hg) atTop
      (𝓝 (modularTomitaLimitVector g hg y)) := by
  have he (n : ℕ) :
      ‖modularTomitaFourierVector D hxy g hg n - modularTomitaLimitVector g hg y‖ ^ 2 =
        ∫ ω : ℝ, ‖g ω • (𝓕 (fun t => modularTomitaKernel n t • D.unitary (-t) x) ω -
          (Real.exp (Real.pi * ω) : ℂ) • y)‖ ^ 2 := by
    rw [vectorLp_norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (modularTomitaFourierVector D hxy g hg n)
      (modularTomitaLimitVector g hg y), modularTomitaFourierVector_ae D hxy g hg n,
      modularTomitaLimitVector_ae g hg y] with ω hs hf hl
    rw [hs, Pi.sub_apply, hf, hl]
    simp only [modularTomitaFourierFunction, modularWeightedFunction, mul_smul, smul_sub]
  have hsq : Tendsto (fun n =>
      ‖modularTomitaFourierVector D hxy g hg n - modularTomitaLimitVector g hg y‖ ^ 2)
      atTop (𝓝 0) :=
    (modularTomitaKernel_weighted_integral_limit_all D hxy g hg).congr'
      (Eventually.of_forall (fun n => (he n).symm))
  have hn := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simp only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] at hn
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn

end WeakPureInfiniteness

end

end OAI
