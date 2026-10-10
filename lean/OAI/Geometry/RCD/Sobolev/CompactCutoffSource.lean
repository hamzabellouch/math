import OAI.Geometry.RCD.Sobolev.MeasureLaplacianProduct

namespace OAI

/-! # Compact support of the full cutoff source -/

open Set MeasureTheory
open scoped BoundedContinuousFunction NNReal

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

omit [MetricSpace X] [BorelSpace X] [ProperSpace X] in
/-- An integrable density vanishing off a measurable set has its whole
signed variation supported there. -/
theorem signedDensity_variation_compl {f : X → ℝ} (hf : Integrable f μ)
    {K : Set X} (hK : MeasurableSet K) (hs : ∀ᵐ x ∂μ, x ∉ K → f x = 0) :
    (μ.withDensityᵥ f).variation Kᶜ = 0 := by
  apply (VectorMeasure.variation_apply_eq_zero hK.compl).2
  intro s hsK hsm
  rw [withDensityᵥ_apply hf hsm]
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_of_ae hs, ae_restrict_mem hsm] with x hx hxs
  exact hx (hsK hxs)

theorem cutoffSourceDensity_zero_off (g c : SobolevSpace μ hQ) (q : Lp ℝ 2 μ)
    (χ : X →ᵇ ℝ) (hc : SobolevSpace.toLp μ hQ c =ᵐ[μ] χ)
    {K : Set X} (hχ : ∀ x ∉ K, χ x = 0)
    (hq : ∀ᵐ x ∂μ, x ∉ K → q x = 0) :
    ∀ᵐ x ∂μ, x ∉ K → cutoffSourceDensity μ hQ g c q x = 0 := by
  filter_upwards [hc, hq, localGamma_zero_on_level μ hQ c g 0,
    localGamma_comm μ hQ g c] with x hcx hqx hz hcomm hx
  have hc0 : SobolevSpace.toLp μ hQ c x = 0 := hcx.trans (hχ x hx)
  simp only [cutoffSourceDensity, hqx hx, hcomm, hz hc0, mul_zero, add_zero]

/-- Both the cutoff function and its full measure Laplacian have the
same support bound as the cutoff and its weak Laplacian. -/
theorem cutoffMeasureSource_variation_compl (g c : SobolevSpace μ hQ) (q : Lp ℝ 2 μ)
    (ν : SignedMeasure X) (χ : X →ᵇ ℝ)
    (hc : SobolevSpace.toLp μ hQ c =ᵐ[μ] χ)
    {K : Set X} (hK : MeasurableSet K) (hχ : ∀ x ∉ K, χ x = 0)
    (hq : ∀ᵐ x ∂μ, x ∉ K → q x = 0) :
    (cutoffMeasureSource μ hQ g c q ν χ).variation Kᶜ = 0 := by
  have hw := signedSourceWeight_variation_compl ν χ hK hχ
  have hd := signedDensity_variation_compl μ (cutoffSourceDensity_integrable μ hQ g c q)
    hK (cutoffSourceDensity_zero_off μ hQ g c q χ hc hχ hq)
  apply (VectorMeasure.variation_apply_eq_zero hK.compl).2
  intro s hs hsm
  rw [cutoffMeasureSource, add_apply,
    (VectorMeasure.variation_apply_eq_zero hK.compl).mp hw s hs hsm,
    (VectorMeasure.variation_apply_eq_zero hK.compl).mp hd s hs hsm, add_zero]

omit [ProperSpace X] [BorelSpace X] in
theorem cutoffProduct_zero_off (g c : SobolevSpace μ hQ) (χ : X →ᵇ ℝ)
    (hc : SobolevSpace.toLp μ hQ c =ᵐ[μ] χ) (D : ℝ≥0)
    (hg : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ g x| ≤ D)
    {K : Set X} (hχ : ∀ x ∉ K, χ x = 0) :
    ∀ᵐ x ∂μ, x ∉ K →
      SobolevSpace.toLp μ hQ (SobolevSpace.product μ hQ g c D ‖χ‖₊) x = 0 := by
  have hcb : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ c x| ≤ (‖χ‖₊ : ℝ) := by
    filter_upwards [hc] with x hx
    simpa only [hx, Real.norm_eq_abs, coe_nnnorm] using χ.norm_coe_le_norm x
  filter_upwards [SobolevSpace.product_coe μ hQ g c D ‖χ‖₊ hg hcb, hc] with x hx hcx hKx
  rw [hx, hcx, hχ x hKx, mul_zero]

end RegularPointCoordinates

end

end OAI
