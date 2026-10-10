import OAI.Geometry.RCD.Sobolev.GoodLaplacianCutoff

namespace OAI

/-! # A genuine local constant is weakly harmonic -/

open Set Metric MeasureTheory

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- Gradient locality on level sets suffices; no global constant Sobolev
function is needed when the ambient measure is infinite. -/
theorem isSobolevHarmonicOn_of_local_constant (s : Set X) (hs : MeasurableSet s)
    (η : SobolevSpace μ hQ) (c : ℝ)
    (hη : SobolevSpace.toLp μ hQ η =ᵐ[μ.restrict s] fun _ => c) :
    IsSobolevHarmonicOn μ hQ s η := by
  intro φ hφ
  have hinside : localGamma μ hQ η φ =ᵐ[μ.restrict s] 0 := by
    filter_upwards [hη, ae_restrict_of_ae (localGamma_zero_on_level μ hQ η φ c)] with x hx hz
    exact hz hx
  have hφzero := SobolevSpace.dirichlet_zero_off μ hQ s hs ⟨φ, hφ⟩
  have houtside : localGamma μ hQ η φ =ᵐ[μ.restrict sᶜ] 0 := by
    filter_upwards [hφzero, ae_restrict_of_ae (localGamma_zero_on_level μ hQ φ η 0),
      ae_restrict_of_ae (localGamma_comm μ hQ η φ)] with x hx hz hc
    exact hc.trans (hz hx)
  have hzero := ae_of_ae_restrict_of_ae_restrict_compl s hinside houtside
  rw [← integral_localGamma_eq_energyForm, integral_congr_ae hzero]
  simp only [Pi.zero_apply, integral_zero]

theorem GoodLaplacianCutoff.harmonic_on_inner_ball {p : X} {r C : ℝ}
    (χ : GoodLaplacianCutoff μ hQ p r C) :
    IsSobolevHarmonicOn μ hQ (ball p r) χ.sobolev := by
  apply isSobolevHarmonicOn_of_local_constant μ hQ _ measurableSet_ball χ.sobolev 1
  filter_upwards [ae_restrict_of_ae χ.representative, ae_restrict_mem measurableSet_ball]
    with x hx hxr
  exact hx.trans (χ.one x hxr)

end RegularPointCoordinates

end

end OAI
