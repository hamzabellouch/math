import OAI.Geometry.RCD.Sobolev.WeightedGammaLocality

namespace OAI

/-! # Local gradient differences are independent of global extensions -/

open Set Filter MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

omit [BorelSpace X] [ProperSpace X] in
theorem toLp_sub_congr_on {Ω : Set X} {u u' v v' : SobolevSpace μ Q}
    (hu : SobolevSpace.toLp μ Q u =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ Q u')
    (hv : SobolevSpace.toLp μ Q v =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ Q v') :
    SobolevSpace.toLp μ Q (u-v) =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ Q (u'-v') := by
  simp only [map_sub]
  filter_upwards [hu,hv,
    ae_restrict_of_ae (Lp.coeFn_sub (SobolevSpace.toLp μ Q u) (SobolevSpace.toLp μ Q v)),
    ae_restrict_of_ae (Lp.coeFn_sub (SobolevSpace.toLp μ Q u') (SobolevSpace.toLp μ Q v'))]
    with x hx hy hxy hxy'
  rw [hxy,hxy']
  simp only [Pi.sub_apply,hx,hy]

theorem weighted_gradient_difference_congr_on {Ω : Set X} (hΩ : MeasurableSet Ω)
    {u u' v v' : SobolevSpace μ Q}
    (hu : SobolevSpace.toLp μ Q u =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ Q u')
    (hv : SobolevSpace.toLp μ Q v =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ Q v')
    (w : X → ℝ) (hw : ∀ x ∉ Ω, w x = 0) :
    weightedGamma μ Q w (u-v) (u-v) = weightedGamma μ Q w (u'-v') (u'-v') :=
  weightedGamma_congr_on μ Q hΩ (toLp_sub_congr_on μ Q hu hv)
    (toLp_sub_congr_on μ Q hu hv) w hw

end RegularPointCoordinates

end

end OAI
