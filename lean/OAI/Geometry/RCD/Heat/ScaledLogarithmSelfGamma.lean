import OAI.Geometry.RCD.Heat.LocalLogarithmGammaByValue

namespace OAI

/-! # The exact energy identity for a locally scaled logarithm -/

open Set Filter MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

theorem scaled_logarithm_self_gamma {Ω : Set X} (u U : SobolevSpace μ Q)
    {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c)
    (hu : ∀ᵐ x ∂μ.restrict Ω, SobolevSpace.toLp μ Q u x ∈ Icc a b)
    (hU : SobolevSpace.toLp μ Q U =ᵐ[μ.restrict Ω]
      fun x => c*Real.log (SobolevSpace.toLp μ Q u x)) :
    (fun x => c^2*localGamma μ Q u u x) =ᵐ[μ.restrict Ω]
      fun x => (SobolevSpace.toLp μ Q u x)^2*localGamma μ Q U U x := by
  let V := c⁻¹ • U
  have hV : SobolevSpace.toLp μ Q V =ᵐ[μ.restrict Ω]
      fun x => Real.log (SobolevSpace.toLp μ Q u x) := by
    filter_upwards [hU,ae_restrict_of_ae (Lp.coeFn_smul c⁻¹ (SobolevSpace.toLp μ Q U))]
      with x hx hs
    change (c⁻¹ • SobolevSpace.toLp μ Q U) x=_
    rw [hs]
    change c⁻¹*SobolevSpace.toLp μ Q U x=_
    rw [hx,← mul_assoc,inv_mul_cancel₀ hc.ne',one_mul]
  have hchain (w : SobolevSpace μ Q) := local_logarithm_gamma_of_value μ Q u V ha hab hu hV w
  have hpos := hu.mono fun x hx => ha.trans_le hx.1
  have hslope := local_logarithmic_minimalSlope μ Q u V hpos hchain
  have hscale : SobolevSpace.minimalSlope μ Q V =ᵐ[μ]
      fun x => c⁻¹*SobolevSpace.minimalSlope μ Q U x := by
    rw [show V=c⁻¹ • U from rfl,SobolevSpace.minimalSlope_smul_nonneg μ Q U (inv_nonneg.mpr hc.le)]
    exact Lp.coeFn_smul _ _
  filter_upwards [hslope,ae_restrict_of_ae hscale,hpos,
    ae_restrict_of_ae (localGamma_self μ Q u),ae_restrict_of_ae (localGamma_self μ Q U)]
    with x hx hy hp huu hUU
  rw [hy] at hx
  have he : c*SobolevSpace.minimalSlope μ Q u x=
      SobolevSpace.toLp μ Q u x*SobolevSpace.minimalSlope μ Q U x := by
    field_simp [hc.ne',hp.ne'] at hx
    linarith only [hx]
  rw [huu,hUU]
  calc
    _ = (c*SobolevSpace.minimalSlope μ Q u x)^2 := by ring
    _ = (SobolevSpace.toLp μ Q u x*SobolevSpace.minimalSlope μ Q U x)^2 := by rw [he]
    _ = _ := by ring

end RegularPointCoordinates

end

end OAI
