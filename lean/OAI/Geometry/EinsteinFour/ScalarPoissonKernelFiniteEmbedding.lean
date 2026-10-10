import OAI.Geometry.EinsteinFour.ScalarPoissonKernelSobolev

namespace OAI

/-! The finite regularity embedding needed before positivity is known:
in four dimensions H⁴ has a C¹ representative.  The proof constructs
that representative by Fourier inversion and controls its first moment. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap ENNReal BoundedContinuousFunction

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)

private def scalarC1Reciprocal (x : V) : ℂ :=
  Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ))

private theorem scalarC1Reciprocal_temperate : scalarC1Reciprocal.HasTemperateGrowth := by
  unfold scalarC1Reciprocal
  fun_prop

private theorem scalarC1Reciprocal_norm (x : V) :
    ‖scalarC1Reciprocal x‖ = (Real.sqrt (1 + ‖x‖ ^ 2))⁻¹ := by
  rw [scalarC1Reciprocal, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos (by positivity) _)]
  rw [show (-1 / 2 : ℝ) = -(1 / 2) by norm_num,
    Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow]

private theorem scalarC1Reciprocal_bound (x : V) : ‖scalarC1Reciprocal x‖ ≤ 1 := by
  rw [scalarC1Reciprocal_norm]
  have hs := Real.sq_sqrt (show 0 ≤ 1 + ‖x‖ ^ 2 by positivity)
  have hnonneg := Real.sqrt_nonneg (1 + ‖x‖ ^ 2)
  have h : 1 ≤ Real.sqrt (1 + ‖x‖ ^ 2) := by nlinarith [sq_nonneg ‖x‖]
  exact inv_le_one_of_one_le₀ h

private theorem scalarC1Reciprocal_first_bound (x : V) :
    ‖x‖ * ‖scalarC1Reciprocal x‖ ≤ 1 := by
  rw [scalarC1Reciprocal_norm]
  have hp : 0 < Real.sqrt (1 + ‖x‖ ^ 2) := Real.sqrt_pos.mpr (by positivity)
  apply (mul_inv_le_iff₀ hp).mpr
  simp only [one_mul]
  nlinarith [Real.sq_sqrt (show 0 ≤ 1 + ‖x‖ ^ 2 by positivity), norm_nonneg x]

private theorem scalarC1Reciprocal_memLp :
    MemLp scalarC1Reciprocal ∞ (volume : Measure V) := by
  let f : V →ᵇ ℂ := BoundedContinuousFunction.ofNormedAddCommGroup
    scalarC1Reciprocal scalarC1Reciprocal_temperate.1.continuous 1 scalarC1Reciprocal_bound
  exact f.memLp_top

/-- H⁴ supplies an L¹ Fourier representative with integrable first moment. -/
theorem scalar_H4_fourier_first_moment (u : 𝓢'(V, ℂ)) (hu : MemSobolev 4 2 u) :
    ∃ v : Lp ℂ 1 (volume : Measure V),
      𝓕 u = (v : 𝓢'(V, ℂ)) ∧ Integrable (fun x : V => ‖x‖ * ‖v x‖) := by
  have hreg : MemSobolev 3 2 (besselPotential V ℂ 1 u) := by
    rw [memSobolev_besselPotential_iff]
    norm_num only [show (1 : ℝ) + 3 = 4 by norm_num]
    exact hu
  obtain ⟨w, hw⟩ := hreg.fourier_memL1 (by
    simp only [finrank_euclideanSpace, Fintype.card_fin]
    norm_num)
  rw [fourier_besselPotential_eq_smulLeftCLM_fourier_apply] at hw
  let hρ := scalarC1Reciprocal_memLp
  let v : Lp ℂ 1 (volume : Measure V) := hρ.toLp • w
  have hmul : (fun x : V => Complex.ofReal ((1 + ‖x‖ ^ 2) ^ ((1 : ℝ) / 2))) *
      scalarC1Reciprocal = fun _ => (1 : ℂ) := by
    ext x
    simp only [Pi.mul_apply, scalarC1Reciprocal]
    rw [show (-1 / 2 : ℝ) = -(1 / 2) by norm_num,
      Real.rpow_neg (by positivity), ← Complex.ofReal_mul,
      mul_inv_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos (by positivity) _)), Complex.ofReal_one]
  have hv : (v : 𝓢'(V, ℂ)) = 𝓕 u := by
    dsimp [v]
    rw [Lp.toTemperedDistribution_smul_eq scalarC1Reciprocal_temperate,
      ← hw, smulLeftCLM_smulLeftCLM_apply (by fun_prop) scalarC1Reciprocal_temperate,
      hmul, smulLeftCLM_const, one_smul]
  have hpoint : ∀ᵐ x ∂(volume : Measure V), v x = scalarC1Reciprocal x * w x := by
    filter_upwards [Lp.coeFn_lpSMul (r := (1 : ℝ≥0∞)) (hρ.toLp) w,
      hρ.coeFn_toLp] with x hx hr
    exact hx.trans (by simp only [smul_eq_mul, Pi.mul_apply, hr])
  refine ⟨v, hv.symm, ?_⟩
  have hm : AEStronglyMeasurable (fun x : V => ‖x‖ * ‖v x‖) :=
    continuous_norm.aestronglyMeasurable.mul (Lp.aestronglyMeasurable v).norm
  apply ((memLp_one_iff_integrable.mp (Lp.memLp w)).norm).mono' hm
  filter_upwards [hpoint] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)),
    hx, norm_mul, ← mul_assoc]
  exact (mul_le_mul_of_nonneg_right (scalarC1Reciprocal_first_bound x)
    (norm_nonneg (w x))).trans_eq (one_mul _)

private theorem scalarC1_inverse_pairing (v : Lp ℂ 1 (volume : Measure V))
    (φ : 𝓢(V, ℂ)) :
    (𝓕⁻ (v : 𝓢'(V, ℂ))) φ = ∫ x : V, φ x * (𝓕⁻ (v : V → ℂ)) x := by
  rw [TemperedDistribution.fourierInv_apply, Lp.toTemperedDistribution_apply]
  have h := VectorFourier.integral_bilin_fourierIntegral_eq_flip
    (ContinuousLinearMap.mul ℂ ℂ) (L := -(innerₗ V))
    (μ := (volume : Measure V)) (ν := (volume : Measure V))
    Real.continuous_fourierChar (by
      change Continuous (fun p : V × V => - inner ℝ p.1 p.2)
      fun_prop)
    (memLp_one_iff_integrable.mp (Lp.memLp v)) φ.integrable
  simpa only [SchwartzMap.fourierInv_coe, VectorFourier.fourierIntegral, Real.fourierInv_eq,
    ContinuousLinearMap.mul_apply', LinearMap.neg_apply, LinearMap.flip_apply,
    innerₗ_apply_apply, neg_neg, real_inner_comm, smul_eq_mul, mul_comm] using h.symm

/-- The C¹ representative is obtained without assuming positivity or any
higher regularity of a nonlinear source. -/
theorem scalar_H4_C1_representative (u : 𝓢'(V, ℂ)) (hu : MemSobolev 4 2 u) :
    ∃ f : V → ℂ, ContDiff ℝ 1 f ∧
      ∀ φ : 𝓢(V, ℂ), u φ = ∫ x : V, φ x * f x := by
  obtain ⟨v, hv, hm⟩ := scalar_H4_fourier_first_moment u hu
  refine ⟨𝓕⁻ (v : V → ℂ), ?_, ?_⟩
  · have hf : ContDiff ℝ 1 (𝓕 (v : V → ℂ)) := by
      apply Real.contDiff_fourier
      intro n hn
      have hn' : n ≤ 1 := by exact_mod_cast hn
      interval_cases n
      · simpa only [pow_zero, one_mul] using
          (memLp_one_iff_integrable.mp (Lp.memLp v)).norm
      · simpa only [pow_one] using hm
    have he : (𝓕⁻ (v : V → ℂ)) = (fun x : V => (𝓕 (v : V → ℂ)) (-x)) := by
      funext x
      exact Real.fourierInv_eq_fourier_neg _ _
    rw [he]
    exact hf.comp (contDiff_id.neg)
  · intro φ
    calc
      u φ = (𝓕⁻ (v : 𝓢'(V, ℂ))) φ := by rw [← hv, fourierInv_fourier_eq]
      _ = _ := scalarC1_inverse_pairing v φ

/-- In particular the C¹ function agrees almost everywhere with an L²
representative of the distribution. -/
theorem scalar_L2_H4_C1_representative (u : Lp ℂ 2 (volume : Measure V))
    (hu : MemSobolev 4 2 (u : 𝓢'(V, ℂ))) :
    ∃ f : V → ℂ, ContDiff ℝ 1 f ∧ (u : V → ℂ) =ᵐ[volume] f := by
  obtain ⟨f, hf, heq⟩ := scalar_H4_C1_representative (u : 𝓢'(V, ℂ)) hu
  refine ⟨f, hf, ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp u).locallyIntegrable (by norm_num)) hf.continuous.locallyIntegrable ?_⟩
  intro ψ hψ hc
  have hc' : HasCompactSupport (Complex.ofRealCLM ∘ ψ) := hc.comp_left rfl
  have hs' : ContDiff ℝ (⊤ : ℕ∞) (Complex.ofRealCLM ∘ ψ) := by fun_prop
  have h := heq (hc'.toSchwartzMap hs')
  rw [Lp.toTemperedDistribution_apply] at h
  change (∫ x : V, (ψ x : ℂ) * u x) = ∫ x : V, (ψ x : ℂ) * f x at h
  simpa only [Complex.real_smul, smul_eq_mul] using h

theorem scalar_L2_H4_C1_real_representative (u : Lp ℂ 2 (volume : Measure V))
    (hu : MemSobolev 4 2 (u : 𝓢'(V, ℂ))) :
    ∃ f : V → ℝ, ContDiff ℝ 1 f ∧ (fun x : V => (u x).re) =ᵐ[volume] f := by
  obtain ⟨f, hf, heq⟩ := scalar_L2_H4_C1_representative u hu
  refine ⟨Complex.reCLM ∘ f, Complex.reCLM.contDiff.comp hf, ?_⟩
  filter_upwards [heq] with x hx
  change (u x).re = (f x).re
  rw [hx]

end
end PositiveEinsteinFour.Geometry

end OAI
