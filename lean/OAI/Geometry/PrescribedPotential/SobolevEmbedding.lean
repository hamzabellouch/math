import Mathlib

namespace OAI

/-! Sobolev Embedding. -/

section

 

noncomputable section
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction ContDiff

namespace SobolevChart
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def inverseWeight (k : ℕ) : E →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x : E => (((1 + ‖x‖ ^ 2) ^ (-(k : ℝ)) : ℝ) : ℂ))
    (by
      have ht : (fun x : E => (((1 + ‖x‖ ^ 2) ^ (-(k : ℝ)) : ℝ) : ℂ)).HasTemperateGrowth := by fun_prop
      exact ht.1.continuous) 1 (by
      intro x
      change ‖(((1 + ‖x‖ ^ 2) ^ (-(k : ℝ)) : ℝ) : ℂ)‖ ≤ 1
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.rpow_pos_of_pos (by positivity : 0 < 1 + ‖x‖ ^ 2) _)]
      exact Real.rpow_le_one_of_one_le_of_nonpos
        (by nlinarith [sq_nonneg ‖x‖] : 1 ≤ 1 + ‖x‖ ^ 2) (neg_nonpos.mpr (Nat.cast_nonneg k)))

lemma inverseWeight_temperate (k : ℕ) :
    (inverseWeight (E := E) k : E → ℂ).HasTemperateGrowth := by
  change (fun x : E => (((1 + ‖x‖ ^ 2) ^ (-(k : ℝ)) : ℝ) : ℂ)).HasTemperateGrowth
  fun_prop

lemma weight_cancel (k : ℕ) (x : E) :
    (((1 + ‖x‖ ^ 2) ^ k : ℝ) : ℂ) * inverseWeight k x = 1 := by
  change (((1 + ‖x‖ ^ 2) ^ k : ℝ) : ℂ) *
    (((1 + ‖x‖ ^ 2) ^ (-(k : ℝ)) : ℝ) : ℂ) = 1
  rw [← Complex.ofReal_mul, ← Complex.ofReal_one, Complex.ofReal_inj]
  rw [← Real.rpow_natCast, ← Real.rpow_add (by positivity), add_neg_cancel, Real.rpow_zero]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma all_even_bessel_fourier_L1 {u : 𝓢'(E, ℂ)}
    (hu : ∀ k : ℕ, MemSobolev (2 * (k : ℝ)) 2 u) (k : ℕ) :
    ∃ v : Lp ℂ 1 (volume : Measure E),
      𝓕 (besselPotential E ℂ (2 * k) u) = (v : 𝓢'(E, ℂ)) := by
  have hm : MemSobolev (2 * ((Module.finrank ℝ E + 1 : ℕ) : ℝ)) 2
      (besselPotential E ℂ (2 * k) u) := by
    rw [memSobolev_besselPotential_iff]
    convert hu (k + (Module.finrank ℝ E + 1)) using 1; push_cast; ring
  exact hm.fourier_memL1 (by push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) (Module.finrank ℝ E)])

 

lemma all_even_fourier_moments {u : 𝓢'(E, ℂ)}
    (hu : ∀ k : ℕ, MemSobolev (2 * (k : ℝ)) 2 u) :
    ∃ v : Lp ℂ 1 (volume : Measure E),
      𝓕 u = (v : 𝓢'(E, ℂ)) ∧
      ∀ n : ℕ, Integrable (fun x => ‖x‖ ^ n * ‖v x‖) := by
  obtain ⟨v, hv⟩ := all_even_bessel_fourier_L1 hu 0
  simp only [Nat.cast_zero, mul_zero, besselPotential_zero,
    ContinuousLinearMap.id_apply] at hv
  refine ⟨v, hv, fun n => ?_⟩
  obtain ⟨w, hw⟩ := all_even_bessel_fourier_L1 hu n
  have hw' : smulLeftCLM ℂ (fun x : E => (((1 + ‖x‖ ^ 2) ^ n : ℝ) : ℂ))
      (𝓕 u) = (w : 𝓢'(E, ℂ)) := by
    rw [fourier_besselPotential_eq_smulLeftCLM_fourier_apply] at hw
    simpa only [mul_div_cancel_left₀ (n : ℝ) (by norm_num : (2 : ℝ) ≠ 0),
      Real.rpow_natCast] using hw
  let b := inverseWeight (E := E) n
  have hb := b.memLp_top (μ := volume)
  have he : (hb.toLp b : Lp ℂ ⊤ volume) • w = v := by
    apply (LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot
      (F := ℂ) (E := E) (μ := volume) (p := 1)))
    change (((hb.toLp b : Lp ℂ ⊤ volume) • w : Lp ℂ 1 volume) : 𝓢'(E, ℂ)) = (v : 𝓢'(E, ℂ))
    rw [Lp.toTemperedDistribution_smul_eq (inverseWeight_temperate n) hb,
      ← hw', smulLeftCLM_smulLeftCLM_apply (by fun_prop) (inverseWeight_temperate n)]
    have hc : (fun x : E => (((1 + ‖x‖ ^ 2) ^ n : ℝ) : ℂ)) * (b : E → ℂ) = fun _ => 1 := by
      ext x
      exact weight_cancel n x
    rw [hc, smulLeftCLM_const, one_smul, hv]
  have he' : ∀ᵐ x, ((1 + ‖x‖ ^ 2) ^ n : ℝ) * ‖v x‖ = ‖w x‖ := by
    have hh := Lp.coeFn_lpSMul (r := 1) (hb.toLp b : Lp ℂ ⊤ volume) w
    rw [he] at hh
    filter_upwards [hh, hb.coeFn_toLp] with x hx hb'
    have hx' : (((1 + ‖x‖ ^ 2) ^ n : ℝ) : ℂ) * v x = w x := by
      rw [hx, Pi.smul_apply', hb', smul_eq_mul, ← mul_assoc, weight_cancel, one_mul]
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ (1 + ‖x‖ ^ 2) ^ n by positivity)] using congrArg norm hx'
  apply (L1.integrable_coeFn w).norm.mono'
    (((continuous_norm.pow n).aestronglyMeasurable).mul (Lp.aestronglyMeasurable v).norm)
  filter_upwards [he'] with x hx
  change ‖‖x‖ ^ n * ‖v x‖‖ ≤ ‖w x‖
  rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg x) n) (norm_nonneg (v x))), ← hx]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply pow_le_pow_left₀ (norm_nonneg _)
  nlinarith [sq_nonneg (‖x‖ - 1 / 2)]

 
def boundedDistribution (f : E →ᵇ ℂ) : 𝓢'(E, ℂ) :=
  (f.memLp_top (μ := volume)).toLp f

lemma boundedDistribution_apply (f : E →ᵇ ℂ) (φ : 𝓢(E, ℂ)) :
    boundedDistribution f φ = ∫ x, φ x • f x := by
  rw [boundedDistribution, Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [(f.memLp_top (μ := volume)).coeFn_toLp] with x hx
  rw [hx]

lemma fourier_L1_distribution (v : Lp ℂ 1 (volume : Measure E)) :
    boundedDistribution (Real.Lp.fourierTransform v) = 𝓕 (v : 𝓢'(E, ℂ)) := by
  ext φ
  rw [boundedDistribution_apply, TemperedDistribution.fourier_apply,
    Lp.toTemperedDistribution_apply]
  symm
  simpa using! VectorFourier.integral_fourierIntegral_smul_eq_flip
    (L := innerₗ E) Real.continuous_fourierChar continuous_inner
    φ.integrable (L1.integrable_coeFn v)

lemma fourierInv_L1_distribution (v : Lp ℂ 1 (volume : Measure E)) :
    boundedDistribution (Real.Lp.fourierTransformInv v) = 𝓕⁻ (v : 𝓢'(E, ℂ)) := by
  ext φ
  rw [boundedDistribution_apply, TemperedDistribution.fourierInv_apply,
    Lp.toTemperedDistribution_apply]
  symm
  simpa [SchwartzMap.fourierInv_coe, Real.fourierInv_eq, VectorFourier.fourierIntegral, real_inner_comm] using!
    VectorFourier.integral_fourierIntegral_smul_eq_flip
      (μ := volume) (ν := volume) (L := -innerₗ E) Real.continuous_fourierChar continuous_inner.neg
      φ.integrable (L1.integrable_coeFn v)

lemma fourier_temperate_of_moments {f : E → ℂ} (hf : AEStronglyMeasurable f)
    (hm : ∀ n : ℕ, Integrable (fun x => ‖x‖ ^ n * ‖f x‖)) :
    (𝓕 f).HasTemperateGrowth := by
  refine ⟨Real.contDiff_fourier (N := ⊤) (fun n _ => hm n), fun n => ?_⟩
  refine ⟨0, ∫ x, ‖VectorFourier.fourierPowSMulRight (innerSL ℝ) f x n‖, fun x => ?_⟩
  rw [Real.iteratedFDeriv_fourier (N := ⊤) (fun k _ => hm k) hf (by simp)]
  simp only [pow_zero, mul_one]
  exact VectorFourier.norm_fourierIntegral_le_integral_norm
    Real.fourierChar volume (innerₗ E) _ x

 

theorem all_even_smooth_representative {u : 𝓢'(E, ℂ)}
    (hu : ∀ k : ℕ, MemSobolev (2 * (k : ℝ)) 2 u) :
    ∃ f : E →ᵇ ℂ, (f : E → ℂ).HasTemperateGrowth ∧ boundedDistribution f = u := by
  obtain ⟨v, hv, hm⟩ := all_even_fourier_moments hu
  refine ⟨Real.Lp.fourierTransformInv v, ?_, ?_⟩
  · have ht := fourier_temperate_of_moments (Lp.aestronglyMeasurable v) hm
    change (fun x : E => 𝓕 (v : E → ℂ) (-x)).HasTemperateGrowth
    fun_prop
  · rw [fourierInv_L1_distribution, ← hv, fourierInv_fourier_eq]

end SobolevChart

end
end

end OAI
