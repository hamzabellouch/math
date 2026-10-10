import OAI.Geometry.RCD.Heat.LocalLogarithmicLaplacian

namespace OAI

/-! # The exact local weak gradient of a logarithm

The mixed chain rule gives the minimal slope, including at zero-gradient
points. Quantitative bounds retain the explicit local lower value.
-/

open Set Filter MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

omit [ProperSpace X] in
theorem local_logarithmic_minimalSlope (u v : SobolevSpace μ hQ) {Ω : Set X}
    (hpos : ∀ᵐ x ∂μ.restrict Ω, 0 < SobolevSpace.toLp μ hQ u x)
    (hchain : ∀ w : SobolevSpace μ hQ, localGamma μ hQ v w =ᵐ[μ.restrict Ω]
      fun x => localGamma μ hQ u w x / SobolevSpace.toLp μ hQ u x) :
    SobolevSpace.minimalSlope μ hQ v =ᵐ[μ.restrict Ω]
      fun x => SobolevSpace.minimalSlope μ hQ u x / SobolevSpace.toLp μ hQ u x := by
  filter_upwards [hpos,hchain u,hchain v,ae_restrict_of_ae (localGamma_comm μ hQ u v),
    ae_restrict_of_ae (localGamma_self μ hQ u),ae_restrict_of_ae (localGamma_self μ hQ v),
    ae_restrict_of_ae ((Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hQ u)),
    ae_restrict_of_ae ((Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hQ v))]
    with x hp hvu hvv hcomm huu hvvself hu0 hv0
  apply (sq_eq_sq₀ hv0 (div_nonneg hu0 hp.le)).mp
  rw [← hvvself,hvv,hcomm,hvu,huu,div_div,div_pow]
  simp only [pow_two]

omit [ProperSpace X] in
theorem local_logarithmic_gradient_le (u v : SobolevSpace μ hQ) {Ω : Set X}
    (L : ℝ≥0) (hL : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ u x ≤ L)
    {a : ℝ} (ha : 0 < a)
    (hvalue : ∀ᵐ x ∂μ.restrict Ω, a ≤ SobolevSpace.toLp μ hQ u x)
    (hchain : ∀ w : SobolevSpace μ hQ, localGamma μ hQ v w =ᵐ[μ.restrict Ω]
      fun x => localGamma μ hQ u w x / SobolevSpace.toLp μ hQ u x) :
    ∀ᵐ x ∂μ.restrict Ω, SobolevSpace.minimalSlope μ hQ v x ≤ (L:ℝ)/a := by
  have hpos := hvalue.mono fun x hx => ha.trans_le hx
  filter_upwards [local_logarithmic_minimalSlope μ hQ u v hpos hchain,
    ae_restrict_of_ae hL,hvalue] with x he hLx hax
  rw [he]
  exact (div_le_div_of_nonneg_right hLx (ha.le.trans hax)).trans
    (div_le_div_of_nonneg_left L.coe_nonneg ha hax)

end RegularPointCoordinates

end

end OAI
