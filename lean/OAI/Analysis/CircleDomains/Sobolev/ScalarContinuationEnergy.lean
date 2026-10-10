import OAI.Analysis.CircleDomains.Topology.CompactScalarContinuation

namespace OAI

/-! The compact continuous continuation retains the sharp source energy
and the zero gradient on the actual complementary set. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]
namespace RetainedRealCircleModel
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d π} {R : RetainedRealCircleModel d π Q}
namespace ScalarWeakLimit
variable {i : Fin m} (W : R.ScalarWeakLimit i)

 theorem planarWeakGradient_energy :
    (∫ x, W.planarWeakGradient x 0 ^ 2 + W.planarWeakGradient x 1 ^ 2) ≤
      ∫ x in realChartDomain d.physicalDomain,
        gradientEnergy (Q i).physical (fun z => sphericalMetricFactor z • 1) x := by
  change (∫ x, W.horizontal (complexPlaneCoordinates x) ^ 2 +
    W.vertical (complexPlaneCoordinates x) ^ 2) ≤ _
  rw [complexPlaneCoordinates_measurePreserving.integral_comp
    complexPlaneCoordinates.toHomeomorph.measurableEmbedding
    (fun z => W.horizontal z ^ 2 + W.vertical z ^ 2)]
  exact W.energy

 theorem planarWeakGradient_energy_integrable :
    Integrable (fun x => W.planarWeakGradient x 0 ^ 2 + W.planarWeakGradient x 1 ^ 2) :=
  (W.planarWeakGradient_memLp 0).integrable_sq.add
    (W.planarWeakGradient_memLp 1).integrable_sq

 theorem continuedScalar_gradient_zero (hsch : PlanarSchoenflies) (hG : IsOpen d.physicalDomain)
    (hπ : Continuous π) (hQ : Continuous (Q i).quotient)
    (hc : ∀ q p, p ∈ connectedComponentIn d.physicalDomainᶜ q → π p = π q)
    (hz : ∀ᶠ p in 𝓝 (π OnePoint.infty), (Q i).quotient p = 0) (j : Fin 2) :
    ∀ᵐ x ∂volume, complexPlaneCoordinates x ∉
      R.limit.function '' (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain) →
      (W.continuedScalar_witness R hsch hG hπ hQ hc hz).weakGrad x j = 0 :=
  W.planarWeakGradient_zero_off_image hsch hG j

 theorem continuedScalar_energy (hsch : PlanarSchoenflies) (hG : IsOpen d.physicalDomain)
    (hπ : Continuous π) (hQ : Continuous (Q i).quotient)
    (hc : ∀ q p, p ∈ connectedComponentIn d.physicalDomainᶜ q → π p = π q)
    (hz : ∀ᶠ p in 𝓝 (π OnePoint.infty), (Q i).quotient p = 0) :
    (∫ x, (W.continuedScalar_witness R hsch hG hπ hQ hc hz).weakGrad x 0 ^ 2 +
      (W.continuedScalar_witness R hsch hG hπ hQ hc hz).weakGrad x 1 ^ 2) ≤
      ∫ x in realChartDomain d.physicalDomain,
        gradientEnergy (Q i).physical (fun z => sphericalMetricFactor z • 1) x :=
  W.planarWeakGradient_energy

end ScalarWeakLimit
end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
