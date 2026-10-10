import Mathlib
import OAI.Geometry.PrescribedPotential.CircleRadialCalculus
import OAI.Geometry.PrescribedPotential.StrongSobolevEmbedding

namespace OAI

/-! Finite Sobolev Embedding. -/

section

 

noncomputable section
open Set Filter Topology MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction ContDiff
namespace SobolevChart
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma fourier_moment_of_bessel {u : 𝓢'(E, ℂ)}
    {v : Lp ℂ 1 (volume : Measure E)} (hv : 𝓕 u = (v : 𝓢'(E,ℂ))) (n : ℕ)
    (w : Lp ℂ 1 (volume : Measure E))
    (hw' : smulLeftCLM ℂ (fun x : E => (((1 + ‖x‖ ^ 2) ^ n : ℝ) : ℂ))
      (𝓕 u) = (w : 𝓢'(E, ℂ))) : Integrable (fun x => ‖x‖^n * ‖v x‖) := by
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

lemma finite_fourier_moments {s : ℝ} {u : 𝓢'(E,ℂ)} (hu : MemSobolev s 2 u)
    (N : ℕ) (hs : (Module.finrank ℝ E : ℝ) < 2*(s - 2*N)) :
    ∃ v : Lp ℂ 1 (volume : Measure E), 𝓕 u = (v : 𝓢'(E,ℂ)) ∧
      ∀ n : ℕ, n ≤ N → Integrable (fun x => ‖x‖^n * ‖v x‖) := by
  obtain ⟨v,hv⟩ := hu.fourier_memL1 (by linarith [Nat.cast_nonneg (α := ℝ) N])
  refine ⟨v,hv,fun n hn => ?_⟩
  have hm : MemSobolev (s - 2*n) 2 (besselPotential E ℂ (2*n) u) := by
    rw [memSobolev_besselPotential_iff]
    simpa only [add_sub_cancel] using hu
  obtain ⟨w,hw⟩ := hm.fourier_memL1 (by
    have hh : (n : ℝ) ≤ N := by exact_mod_cast hn
    linarith)
  apply fourier_moment_of_bessel hv n w
  rw [fourier_besselPotential_eq_smulLeftCLM_fourier_apply] at hw
  simpa only [mul_div_cancel_left₀ (n : ℝ) (by norm_num : (2 : ℝ) ≠ 0),
    Real.rpow_natCast] using hw

lemma strongEmbedding_contDiff (s : ℝ) (hs : (Module.finrank ℝ E : ℝ) < 2*s)
    (N : ℕ) (hN : (Module.finrank ℝ E : ℝ) < 2*(s - 2*N)) (u : L2 E) :
    ContDiff ℝ N (strongEmbedding s hs u : E → ℂ) := by
  obtain ⟨v,hv,hm⟩ := finite_fourier_moments (realize_memSobolev s u) N hN
  have he : strongEmbedding s hs u = Real.Lp.fourierTransformInv v := by
    apply boundedDistribution_injective
    rw [strongEmbedding_distribution, boundedDistributionCLM_apply,
      fourierInv_L1_distribution, ← hv, fourierInv_fourier_eq]
  rw [he]
  change ContDiff ℝ N (fun x : E => 𝓕 (v : E → ℂ) (-x))
  have hf : ContDiff ℝ N (𝓕 (v : E → ℂ)) := Real.contDiff_fourier (N := N) (by
    intro n hn
    exact hm n (by exact_mod_cast hn))
  exact hf.comp contDiff_neg
end SobolevChart

end
end

end OAI
