import OAI.Geometry.RCD.Sobolev.PoissonLocality

namespace OAI

/-! # Energy locality against a supported Sobolev test -/

open Set Filter MeasureTheory

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

theorem energyForm_eq_of_test_support {Ω : Set X} (hΩ : MeasurableSet Ω)
    {f g w : SobolevSpace μ hQ}
    (hfg : SobolevSpace.toLp μ hQ f =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ hQ g)
    (v : X → ℝ) (hw : SobolevSpace.toLp μ hQ w =ᵐ[μ] v) (hs : tsupport v ⊆ Ω) :
    energyForm μ hQ f w = energyForm μ hQ g w := by
  rw [← integral_localGamma_eq_energyForm, ← integral_localGamma_eq_energyForm]
  have hfg' := (ae_restrict_iff' hΩ).mp hfg
  apply integral_congr_ae
  filter_upwards [hfg', hw, localGamma_eq_on_eq μ hQ f g w,
    localGamma_comm μ hQ f w, localGamma_comm μ hQ g w,
    localGamma_zero_on_level μ hQ w f 0, localGamma_zero_on_level μ hQ w g 0]
    with x hx hwx hlocal hcf hcg hzf hzg
  by_cases hmem : x ∈ Ω
  · exact hlocal (hx hmem)
  · have hv : v x = 0 := image_eq_zero_of_notMem_tsupport (fun hm => hmem (hs hm))
    rw [hcf, hcg, hzf (hwx.trans hv), hzg (hwx.trans hv)]

end RegularPointCoordinates

end OAI
