import OAI.Geometry.RCD.Transport.RadialTransportIdentity

namespace OAI

/-! # The weak transport balance after substituting the Euler equation -/

open Set MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- Substitution into the proved weak product identity gives the exact
balance used by radial transport. The forcing is an actual L2 function. -/
theorem radial_transport_euler_identity (Ω : Set X) (hΩ : MeasurableSet Ω)
    (f w η : SobolevSpace μ hQ) {a : ℝ}
    (hf : IsConstantLaplacianOn μ hQ Ω f a) (C D L : ℝ≥0)
    (hw : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ w x| ≤ C)
    (χ : X → ℝ) (hχ : LipschitzWith L χ) (hcpt : HasCompactSupport χ)
    (hbound : ∀ x, |χ x| ≤ D) (hnonneg : ∀ x, 0 ≤ χ x)
    (hsupp : tsupport χ ⊆ Ω) (hη : SobolevSpace.toLp μ hQ η =ᵐ[μ] χ)
    (F : X → ℝ) (hF : MemLp F 2 μ)
    (heuler : localGamma μ hQ f w =ᵐ[μ.restrict Ω]
      fun x => SobolevSpace.toLp μ hQ w x + F x / 2) :
    (∫ x in Ω, ((a + 2) * χ x + localGamma μ hQ f η x) *
      (SobolevSpace.toLp μ hQ w x) ^ 2 ∂μ) =
      -(∫ x in Ω, χ x * (SobolevSpace.toLp μ hQ w x * F x) ∂μ) := by
  let W : X → ℝ := SobolevSpace.toLp μ hQ w
  have hW : MemLp W 2 μ := Lp.memLp (SobolevSpace.toLp μ hQ w)
  have hχnorm : ∀ᵐ x ∂μ, ‖χ x‖ ≤ D := Filter.Eventually.of_forall fun x => by
    simpa only [Real.norm_eq_abs] using hbound x
  have hI : Integrable (fun x => χ x * (W x) ^ 2) μ :=
    hW.integrable_sq.bdd_mul hχ.continuous.aestronglyMeasurable hχnorm
  have hIF : Integrable (fun x => χ x * (W x * F x)) μ :=
    (hW.integrable_mul hF).bdd_mul hχ.continuous.aestronglyMeasurable hχnorm
  have hWsq : ∀ᵐ x ∂μ, ‖(W x) ^ 2‖ ≤ (C : ℝ) ^ 2 := by
    filter_upwards [hw] with x hx
    change ‖(SobolevSpace.toLp μ hQ w x) ^ 2‖ ≤ _
    rw [Real.norm_eq_abs, abs_pow, sq_abs]
    have hh := (sq_le_sq₀ (abs_nonneg _) C.coe_nonneg).mpr hx
    rwa [sq_abs] at hh
  have hJ : Integrable (fun x => (W x) ^ 2 * localGamma μ hQ f η x) μ :=
    (localGamma_memL1 μ hQ f η).bdd_mul (hW.aestronglyMeasurable.pow 2) hWsq
  have hb := radial_transport_weak_identity μ hQ Ω hΩ f w η hf C D L hw χ hχ hcpt hbound hnonneg hsupp hη
  have heq : (fun x => 2 * χ x * SobolevSpace.toLp μ hQ w x * localGamma μ hQ f w x +
      (SobolevSpace.toLp μ hQ w x) ^ 2 * localGamma μ hQ f η x) =ᵐ[μ.restrict Ω]
      fun x => 2 * (χ x * (W x) ^ 2) + χ x * (W x * F x) + (W x) ^ 2 * localGamma μ hQ f η x := by
    filter_upwards [heuler] with x hx
    rw [hx]
    dsimp only [W]
    ring
  rw [integral_congr_ae heq] at hb
  have hsplit := integral_add (μ := μ.restrict Ω)
    (((hI.const_mul 2).add hIF).integrableOn) hJ.integrableOn
  simp only [Pi.add_apply] at hsplit
  rw [hsplit, integral_add (hI.const_mul 2).integrableOn hIF.integrableOn,
    integral_const_mul] at hb
  have hleft : (∫ x in Ω, ((a + 2) * χ x + localGamma μ hQ f η x) * (W x) ^ 2 ∂μ) =
      (a + 2) * (∫ x in Ω, χ x * (W x) ^ 2 ∂μ) +
        ∫ x in Ω, (W x) ^ 2 * localGamma μ hQ f η x ∂μ := by
    calc
      _ = ∫ x in Ω, (a + 2) * (χ x * (W x) ^ 2) + (W x) ^ 2 * localGamma μ hQ f η x ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by ring
      _ = _ := by rw [integral_add (hI.const_mul (a + 2)).integrableOn hJ.integrableOn, integral_const_mul]
  change (∫ x in Ω, ((a + 2) * χ x + localGamma μ hQ f η x) * (W x) ^ 2 ∂μ) = _
  rw [hleft]
  linarith only [hb]

end RegularPointCoordinates

end

end OAI
