import OAI.Geometry.RCD.Harmonic.HarmonicQuadraticPotential
import OAI.Geometry.RCD.Sobolev.WeakRadialCancellation

namespace OAI

/-! # The weak transport identity tested on the unnormalized residual -/

open Set MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- The actual compact test χ w² is admissible in the local constant
Laplacian equation. This proves the transport balance before any division
by the inner-ball norm of w. -/
theorem radial_transport_weak_identity (Ω : Set X) (hΩ : MeasurableSet Ω)
    (f w η : SobolevSpace μ hQ) {a : ℝ}
    (hf : IsConstantLaplacianOn μ hQ Ω f a) (C D L : ℝ≥0)
    (hw : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ w x| ≤ C)
    (χ : X → ℝ) (hχ : LipschitzWith L χ) (hcpt : HasCompactSupport χ)
    (hbound : ∀ x, |χ x| ≤ D) (hnonneg : ∀ x, 0 ≤ χ x)
    (hsupp : tsupport χ ⊆ Ω) (hη : SobolevSpace.toLp μ hQ η =ᵐ[μ] χ) :
    (∫ x in Ω, 2 * χ x * SobolevSpace.toLp μ hQ w x * localGamma μ hQ f w x +
      (SobolevSpace.toLp μ hQ w x) ^ 2 * localGamma μ hQ f η x ∂μ) =
      -a * ∫ x in Ω, χ x * (SobolevSpace.toLp μ hQ w x) ^ 2 ∂μ := by
  let w₂ := SobolevSpace.square μ hQ w C
  have hw₂ : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ w₂ x| ≤ (C * C : ℝ≥0) := by
    filter_upwards [SobolevSpace.square_coe μ hQ w C hw, hw] with x hx hb
    change |SobolevSpace.toLp μ hQ (SobolevSpace.square μ hQ w C) x| ≤ _
    rw [hx, abs_pow, sq_abs]
    have hb₂ := (sq_le_sq₀ (abs_nonneg _) C.coe_nonneg).mpr hb
    rw [sq_abs] at hb₂
    simpa only [NNReal.coe_mul, pow_two] using hb₂
  have hηb : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ η x| ≤ D := by
    filter_upwards [hη] with x hx
    rw [hx]
    exact hbound x
  let q := SobolevSpace.product μ hQ η w₂ D (C * C)
  have hq : q ∈ SobolevSpace.dirichlet μ hQ Ω :=
    bounded_cutoff_product_mem_dirichlet μ hQ Ω η w₂ D (C * C) L χ
      hχ hcpt hbound hnonneg hsupp hη hw₂
  have he := hf q hq
  rw [← integral_localGamma_dirichlet μ hQ Ω hΩ f ⟨q, hq⟩] at he
  have hleft : (∫ x in Ω, localGamma μ hQ f q x ∂μ) =
      ∫ x in Ω, 2 * χ x * SobolevSpace.toLp μ hQ w x * localGamma μ hQ f w x +
        (SobolevSpace.toLp μ hQ w x) ^ 2 * localGamma μ hQ f η x ∂μ := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (localGamma_product_right μ hQ f η w₂ D (C * C) hηb hw₂),
      ae_restrict_of_ae (localGamma_square μ hQ w f C hw),
      ae_restrict_of_ae (localGamma_comm μ hQ f w₂),
      ae_restrict_of_ae (localGamma_comm μ hQ f w),
      ae_restrict_of_ae (SobolevSpace.square_coe μ hQ w C hw), ae_restrict_of_ae hη]
      with x hp hs hc hcw hsquare hηx
    change localGamma μ hQ f (SobolevSpace.product μ hQ η w₂ D (C * C)) x = _
    rw [hp, hηx, hc]
    change _ = _ at hsquare
    rw [show SobolevSpace.toLp μ hQ w₂ x = (SobolevSpace.toLp μ hQ w x) ^ 2 from hsquare,
      show localGamma μ hQ w₂ f x = 2 * SobolevSpace.toLp μ hQ w x * localGamma μ hQ w f x from hs,
      ← hcw]
    ring
  have hright : (∫ x in Ω, SobolevSpace.toLp μ hQ q x ∂μ) =
      ∫ x in Ω, χ x * (SobolevSpace.toLp μ hQ w x) ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (SobolevSpace.product_coe μ hQ η w₂ D (C * C) hηb hw₂),
      ae_restrict_of_ae (SobolevSpace.square_coe μ hQ w C hw), ae_restrict_of_ae hη]
      with x hp hs hηx
    change SobolevSpace.toLp μ hQ (SobolevSpace.product μ hQ η w₂ D (C * C)) x = _
    rw [hp, hηx]
    rw [show SobolevSpace.toLp μ hQ w₂ x = (SobolevSpace.toLp μ hQ w x) ^ 2 from hs]
  rwa [hleft, hright] at he

end RegularPointCoordinates

end

end OAI
