import OAI.Geometry.EinsteinFour.ScalarPoissonKernelHelmholtz
import Mathlib.Analysis.Fourier.FourierTransformDeriv

namespace OAI

/-! Arbitrarily high scalar Sobolev regularity produces a smooth function.
The representative is constructed by inverse Fourier integration, rather than
assumed as an elliptic regularity input. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap ENNReal BoundedContinuousFunction

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

private def sobolevReciprocal (n : ℕ) (x : E) : ℂ :=
  Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-(n : ℝ)))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem sobolevReciprocal_temperate (n : ℕ) :
    (sobolevReciprocal (E := E) n).HasTemperateGrowth := by
  unfold sobolevReciprocal
  fun_prop

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem sobolevReciprocal_norm (n : ℕ) (x : E) :
    ‖sobolevReciprocal n x‖ = ((1 + ‖x‖ ^ 2) ^ n)⁻¹ := by
  rw [sobolevReciprocal, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_pos (Real.rpow_pos_of_pos (show 0 < 1 + ‖x‖ ^ 2 by positivity) _)]
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast]

private theorem sobolevReciprocal_memLp (n : ℕ) :
    MemLp (sobolevReciprocal (E := E) n) ∞ (volume : Measure E) := by
  let f : E →ᵇ ℂ := BoundedContinuousFunction.ofNormedAddCommGroup
    (sobolevReciprocal n) (sobolevReciprocal_temperate n).1.continuous 1 (by
      intro x
      rw [sobolevReciprocal_norm]
      exact inv_le_one_of_one_le₀ (one_le_pow₀ (by nlinarith [sq_nonneg ‖x‖])))
  exact f.memLp_top

private theorem scalar_fourier_weight_memL1 (u : 𝓢'(E, ℂ))
    (hu : ∀ n : ℕ, MemSobolev (n : ℝ) 2 u) (k : ℕ) :
    ∃ w : Lp ℂ 1 (volume : Measure E),
      smulLeftCLM ℂ (fun x : E => Complex.ofReal ((1 + ‖x‖ ^ 2) ^ k)) (𝓕 u) = w := by
  let d := Module.finrank ℝ E
  have hdim : (Module.finrank ℝ E : ℝ) < 2 * ((d + 1 : ℕ) : ℝ) := by
    dsimp [d]
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) (Module.finrank ℝ E)]
  have hreg : MemSobolev ((d + 1 : ℕ) : ℝ) 2
      (besselPotential E ℂ (2 * (k : ℝ)) u) := by
    rw [memSobolev_besselPotential_iff]
    convert hu (2 * k + (d + 1)) using 1
    push_cast
    ring
  obtain ⟨w, hw⟩ := hreg.fourier_memL1 hdim
  refine ⟨w, ?_⟩
  rw [fourier_besselPotential_eq_smulLeftCLM_fourier_apply] at hw
  convert hw using 1
  congr 1
  ext x
  simp only [mul_div_cancel_left₀ (k : ℝ) (by norm_num : (2 : ℝ) ≠ 0),
    Real.rpow_natCast]

/-- Every polynomial moment of the Fourier representative is integrable. -/
theorem scalar_sobolev_fourier_moments (u : 𝓢'(E, ℂ))
    (hu : ∀ n : ℕ, MemSobolev (n : ℝ) 2 u)
    (v : Lp ℂ 1 (volume : Measure E)) (hv : 𝓕 u = (v : 𝓢'(E, ℂ)))
    (n : ℕ) : Integrable (fun x : E => ‖x‖ ^ n * ‖v x‖) := by
  obtain ⟨w, hw⟩ := scalar_fourier_weight_memL1 u hu n
  let hρ := sobolevReciprocal_memLp (E := E) n
  let v' : Lp ℂ 1 (volume : Measure E) := hρ.toLp • w
  have heq : (v' : 𝓢'(E, ℂ)) = v := by
    dsimp [v']
    rw [Lp.toTemperedDistribution_smul_eq (sobolevReciprocal_temperate n),
      ← hw, smulLeftCLM_smulLeftCLM_apply (by fun_prop)
        (sobolevReciprocal_temperate n)]
    have hm : (fun x : E => Complex.ofReal ((1 + ‖x‖ ^ 2) ^ n)) *
        sobolevReciprocal n = fun _ : E => (1 : ℂ) := by
      ext x
      simp only [Pi.mul_apply, sobolevReciprocal]
      rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← Complex.ofReal_mul]
      simp [ne_of_gt (show 0 < (1 + ‖x‖ ^ 2) ^ n by positivity)]
    rw [hm, smulLeftCLM_const, one_smul, hv]
  have hv' : v' = v :=
    (LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot
      (F := ℂ) (μ := (volume : Measure E)))) heq
  have hpoint : ∀ᵐ x ∂(volume : Measure E),
      v x = sobolevReciprocal n x * w x := by
    filter_upwards [Lp.coeFn_lpSMul (r := (1 : ℝ≥0∞)) (hρ.toLp) w,
      hρ.coeFn_toLp] with x hx hρx
    rw [← hv']
    exact hx.trans (by simp only [smul_eq_mul, Pi.mul_apply, hρx])
  have hmeas : AEStronglyMeasurable (fun x : E => ‖x‖ ^ n * ‖v x‖)
      (volume : Measure E) :=
    ((continuous_norm.pow n).aestronglyMeasurable).mul (Lp.aestronglyMeasurable v).norm
  refine ((memLp_one_iff_integrable.mp (Lp.memLp w)).norm).mono' hmeas ?_
  filter_upwards [hpoint] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hx, norm_mul, ← mul_assoc]
  have hb : 0 < (1 + ‖x‖ ^ 2) ^ n := by positivity
  have hp : ‖x‖ ^ n ≤ (1 + ‖x‖ ^ 2) ^ n := by
    gcongr
    nlinarith [sq_nonneg (‖x‖ - 1)]
  have hc : ‖x‖ ^ n * ‖sobolevReciprocal n x‖ ≤ 1 := by
    rw [sobolevReciprocal_norm]
    simpa only [mul_inv_cancel₀ hb.ne'] using
      mul_le_mul_of_nonneg_right hp (inv_nonneg.mpr hb.le)
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hc (norm_nonneg (w x))

private theorem inverse_fourier_pairing (v : Lp ℂ 1 (volume : Measure E))
    (φ : 𝓢(E, ℂ)) :
    (𝓕⁻ (v : 𝓢'(E, ℂ))) φ =
      ∫ x : E, φ x * (𝓕⁻ (v : E → ℂ)) x := by
  rw [TemperedDistribution.fourierInv_apply, Lp.toTemperedDistribution_apply]
  have h := VectorFourier.integral_bilin_fourierIntegral_eq_flip
    (ContinuousLinearMap.mul ℂ ℂ) (L := -(innerₗ E))
    (μ := (volume : Measure E)) (ν := (volume : Measure E))
    Real.continuous_fourierChar (by
      change Continuous (fun p : E × E => - inner ℝ p.1 p.2)
      fun_prop)
    (memLp_one_iff_integrable.mp (Lp.memLp v)) φ.integrable
  simpa only [SchwartzMap.fourierInv_coe, VectorFourier.fourierIntegral, Real.fourierInv_eq,
    ContinuousLinearMap.mul_apply', LinearMap.neg_apply, LinearMap.flip_apply,
    innerₗ_apply_apply, neg_neg, real_inner_comm,
    smul_eq_mul, mul_comm] using h.symm

/-- Arbitrarily high L2 Sobolev regularity gives an actual smooth representative,
with equality against every Schwartz test function. -/
theorem scalar_sobolev_smooth_representative (u : 𝓢'(E, ℂ))
    (hu : ∀ n : ℕ, MemSobolev (n : ℝ) 2 u) :
    ∃ f : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) f ∧
      ∀ φ : 𝓢(E, ℂ), u φ = ∫ x : E, φ x * f x := by
  obtain ⟨v, hv⟩ := scalar_fourier_weight_memL1 u hu 0
  simp only [pow_zero, Complex.ofReal_one, smulLeftCLM_const, one_smul] at hv
  refine ⟨𝓕⁻ (v : E → ℂ), ?_, ?_⟩
  · have hf : ContDiff ℝ (⊤ : ℕ∞) (𝓕 (v : E → ℂ)) :=
      Real.contDiff_fourier (fun n _ => scalar_sobolev_fourier_moments u hu v hv n)
    have he : (𝓕⁻ (v : E → ℂ)) = (fun x : E => (𝓕 (v : E → ℂ)) (-x)) := by
      funext x
      exact Real.fourierInv_eq_fourier_neg _ _
    rw [he]
    exact hf.comp (contDiff_id.neg)
  · intro φ
    calc
      u φ = (𝓕⁻ (v : 𝓢'(E, ℂ))) φ := by rw [← hv, fourierInv_fourier_eq]
      _ = _ := inverse_fourier_pairing v φ

/-- For an L2 function, the constructed smooth function agrees almost everywhere
with the original representative. -/
theorem scalar_L2_sobolev_smooth_representative (u : Lp ℂ 2 (volume : Measure E))
    (hu : ∀ n : ℕ, MemSobolev (n : ℝ) 2 (u : 𝓢'(E, ℂ))) :
    ∃ f : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) f ∧ (u : E → ℂ) =ᵐ[volume] f := by
  obtain ⟨f, hf, heq⟩ := scalar_sobolev_smooth_representative (u : 𝓢'(E, ℂ)) hu
  refine ⟨f, hf, ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp u).locallyIntegrable (by norm_num)) hf.continuous.locallyIntegrable ?_⟩
  intro ψ hψ hc
  have hc' : HasCompactSupport (Complex.ofRealCLM ∘ ψ) := hc.comp_left rfl
  have hs' : ContDiff ℝ (⊤ : ℕ∞) (Complex.ofRealCLM ∘ ψ) := by fun_prop
  have h := heq (hc'.toSchwartzMap hs')
  rw [Lp.toTemperedDistribution_apply] at h
  change (∫ x : E, (ψ x : ℂ) * u x) = ∫ x : E, (ψ x : ℂ) * f x at h
  simpa only [Complex.real_smul, smul_eq_mul] using h

/-- The real part inherits a smooth representative without requiring a
complex-valued formulation from a geometric caller. -/
theorem scalar_L2_sobolev_smooth_real_representative
    (u : Lp ℂ 2 (volume : Measure E))
    (hu : ∀ n : ℕ, MemSobolev (n : ℝ) 2 (u : 𝓢'(E, ℂ))) :
    ∃ f : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧
      (fun x : E => (u x).re) =ᵐ[volume] f := by
  obtain ⟨f, hf, heq⟩ := scalar_L2_sobolev_smooth_representative u hu
  refine ⟨Complex.reCLM ∘ f, Complex.reCLM.contDiff.comp hf, ?_⟩
  filter_upwards [heq] with x hx
  change (u x).re = (f x).re
  rw [hx]

end
end PositiveEinsteinFour.Geometry

end OAI
