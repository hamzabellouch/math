import OAI.Geometry.RCD.Sobolev.WeakRadialCancellation
import OAI.Geometry.RCD.Sobolev.SupportedEnergyLocality
import OAI.Geometry.RCD.Coordinates.BoundedSplittingCoordinates

namespace OAI

/-! # Locality of integrated Hessian pairings -/

open Set Filter MeasureTheory

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- A zero-boundary test sees only the potential inside its domain. -/
theorem localGamma_eq_of_dirichlet_right {Ω : Set X} (hΩ : MeasurableSet Ω)
    {f g : SobolevSpace μ hQ}
    (hfg : SobolevSpace.toLp μ hQ f =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ hQ g)
    (φ : SobolevSpace.dirichlet μ hQ Ω) :
    localGamma μ hQ f φ.val =ᵐ[μ] localGamma μ hQ g φ.val := by
  have hzero := (ae_restrict_iff' hΩ.compl).mp (SobolevSpace.dirichlet_zero_off μ hQ Ω hΩ φ)
  have heq := (ae_restrict_iff' hΩ).mp hfg
  filter_upwards [heq,hzero,localGamma_eq_on_eq μ hQ f g φ.val,
    localGamma_zero_on_level μ hQ φ.val f 0,localGamma_zero_on_level μ hQ φ.val g 0,
    localGamma_comm μ hQ f φ.val,localGamma_comm μ hQ g φ.val] with x he hz hg hf0 hg0 hfcomm hgcomm
  by_cases hx : x ∈ Ω
  · exact hg (he hx)
  · rw [hfcomm,hgcomm,hf0 (hz hx),hg0 (hz hx)]

theorem energyForm_eq_of_dirichlet {Ω : Set X} (hΩ : MeasurableSet Ω)
    {f g : SobolevSpace μ hQ}
    (hfg : SobolevSpace.toLp μ hQ f =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ hQ g)
    (φ : SobolevSpace.dirichlet μ hQ Ω) :
    energyForm μ hQ f φ.val = energyForm μ hQ g φ.val := by
  rw [← integral_localGamma_eq_energyForm,← integral_localGamma_eq_energyForm]
  exact integral_congr_ae (localGamma_eq_of_dirichlet_right μ hQ hΩ hfg φ)

/-- Replacing either potential outside the domain preserves the complete
integrated Hessian data, including its dense core. -/
def LocalHessianPairing.congr {Ω : Set X} (hΩ : MeasurableSet Ω)
    {f a F A : SobolevSpace μ hQ}
    (G : LocalHessianPairing μ hQ Ω F A)
    (hf : SobolevSpace.toLp μ hQ F =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ hQ f)
    (ha : SobolevSpace.toLp μ hQ A =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ hQ a) :
    LocalHessianPairing μ hQ Ω f a where
  mixed := G.mixed
  mixed_rep := G.mixed_rep.trans (localGamma_pair_congr_ae μ hQ hf ha)
  core := G.core
  core_dense := G.core_dense
  gammaF := G.gammaF
  gammaA := G.gammaA
  gammaF_rep := fun φ => (G.gammaF_rep φ).trans
    (localGamma_eq_of_dirichlet_right μ hQ hΩ hf φ.val)
  gammaA_rep := fun φ => (G.gammaA_rep φ).trans
    (localGamma_eq_of_dirichlet_right μ hQ hΩ ha φ.val)
  hessian := G.hessian
  koszul := by
    intro φ
    rw [← energyForm_eq_of_dirichlet μ hQ hΩ ha (G.gammaF φ),
      ← energyForm_eq_of_dirichlet μ hQ hΩ hf (G.gammaA φ)]
    exact G.koszul φ

end RegularPointCoordinates

end

end OAI
