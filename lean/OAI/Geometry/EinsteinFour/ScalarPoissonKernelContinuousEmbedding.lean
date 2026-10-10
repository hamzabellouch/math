import OAI.Geometry.EinsteinFour.ScalarPoissonKernelFiniteEmbedding

namespace OAI

/-! The finite H3 embedding needed for weak positivity.  Fourier inversion
provides a bounded continuous representative before any positivity or smooth
nonlinear chain rule is available. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap ENNReal BoundedContinuousFunction

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)

private def h3InverseBounded (v : Lp ℂ 1 (volume : Measure V)) : V →ᵇ ℂ :=
  Real.Lp.fourierTransformInv v

private theorem h3InverseBounded_apply (v : Lp ℂ 1 (volume : Measure V)) (x : V) :
    h3InverseBounded v x = (𝓕⁻ (v : V → ℂ)) x := by
  exact Real.Lp.fourierTransformInv_apply v x

private theorem h3_inverse_pairing (v : Lp ℂ 1 (volume : Measure V))
    (φ : 𝓢(V, ℂ)) :
    (𝓕⁻ (v : 𝓢'(V, ℂ))) φ = ∫ x : V, φ x * h3InverseBounded v x := by
  simp_rw [h3InverseBounded_apply]
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

/-- Three L2 Sobolev derivatives in dimension four produce a bounded continuous
function representing the same tempered distribution. -/
theorem scalar_H3_boundedContinuous_representative (u : 𝓢'(V, ℂ))
    (hu : MemSobolev 3 2 u) :
    ∃ f : V →ᵇ ℂ, ∀ φ : 𝓢(V, ℂ), u φ = ∫ x : V, φ x * f x := by
  obtain ⟨v, hv⟩ := hu.fourier_memL1 (by
    simp only [finrank_euclideanSpace, Fintype.card_fin]
    norm_num)
  refine ⟨h3InverseBounded v, fun φ => ?_⟩
  calc
    u φ = (𝓕⁻ (v : 𝓢'(V, ℂ))) φ := by rw [← hv, fourierInv_fourier_eq]
    _ = _ := h3_inverse_pairing v φ

/-- The bounded continuous representative agrees almost everywhere with any
L2 realization of the original distribution. -/
theorem scalar_L2_H3_boundedContinuous_representative
    (u : Lp ℂ 2 (volume : Measure V)) (hu : MemSobolev 3 2 (u : 𝓢'(V, ℂ))) :
    ∃ f : V →ᵇ ℂ, (u : V → ℂ) =ᵐ[volume] f := by
  obtain ⟨f, heq⟩ := scalar_H3_boundedContinuous_representative (u : 𝓢'(V, ℂ)) hu
  refine ⟨f, ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp u).locallyIntegrable (by norm_num)) f.continuous.locallyIntegrable ?_⟩
  intro ψ hψ hc
  have hc' : HasCompactSupport (Complex.ofRealCLM ∘ ψ) := hc.comp_left rfl
  have hs' : ContDiff ℝ (⊤ : ℕ∞) (Complex.ofRealCLM ∘ ψ) := by fun_prop
  have h := heq (hc'.toSchwartzMap hs')
  rw [Lp.toTemperedDistribution_apply] at h
  change (∫ x : V, (ψ x : ℂ) * u x) = ∫ x : V, (ψ x : ℂ) * f x at h
  simpa only [Complex.real_smul, smul_eq_mul] using h

theorem scalar_L2_H3_continuous_representative
    (u : Lp ℂ 2 (volume : Measure V)) (hu : MemSobolev 3 2 (u : 𝓢'(V, ℂ))) :
    ∃ f : V → ℂ, Continuous f ∧ (u : V → ℂ) =ᵐ[volume] f := by
  obtain ⟨f, hf⟩ := scalar_L2_H3_boundedContinuous_representative u hu
  exact ⟨f, f.continuous, hf⟩

theorem scalar_L2_H3_continuous_real_representative
    (u : Lp ℂ 2 (volume : Measure V)) (hu : MemSobolev 3 2 (u : 𝓢'(V, ℂ))) :
    ∃ f : V → ℝ, Continuous f ∧ (fun x : V => (u x).re) =ᵐ[volume] f := by
  obtain ⟨f, hf, heq⟩ := scalar_L2_H3_continuous_representative u hu
  refine ⟨Complex.reCLM ∘ f, Complex.reCLM.continuous.comp hf, ?_⟩
  filter_upwards [heq] with x hx
  exact congrArg Complex.re hx

end
end PositiveEinsteinFour.Geometry

end OAI
