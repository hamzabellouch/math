import OAI.Analysis.CircleDomains.Sobolev.ScalarContinuationEnergy

namespace OAI

/-! Actual Sobolev continuations of the retained smooth scalar tests.
The exterior coefficient area theorem controls the weak limits. -/
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
  {Q : Fin m → PhysicalRealCoordinate d π} (R : RetainedRealCircleModel d π Q)

 theorem exists_continuation_witness (harea : ExteriorCoefficientAreaTheorem)
    (hsch : PlanarSchoenflies) (hG : IsOpen d.physicalDomain)
    (hπ : Continuous π) (i : Fin m) (hQ : Continuous (Q i).quotient)
    (hc : ∀ q p, p ∈ connectedComponentIn d.physicalDomainᶜ q → π p = π q)
    (hz : ∀ᶠ p in 𝓝 (π OnePoint.infty), (Q i).quotient p = 0) :
    ∃ H : DeGiorgi.MemW1pWitness 2
      (fun x => R.continuedScalar hG i (complexPlaneCoordinates x)) univ,
      (∀ j : Fin 2, ∀ᵐ x ∂volume, complexPlaneCoordinates x ∉
        R.limit.function '' (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain) → H.weakGrad x j = 0) ∧
      Integrable (fun x => H.weakGrad x 0 ^ 2 + H.weakGrad x 1 ^ 2) ∧
      (∫ x, H.weakGrad x 0 ^ 2 + H.weakGrad x 1 ^ 2) ≤
        ∫ x in realChartDomain d.physicalDomain,
          gradientEnergy (Q i).physical (fun z => sphericalMetricFactor z • 1) x := by
  obtain ⟨W⟩ := R.exists_scalar_weak_limit harea i hQ
  exact ⟨W.continuedScalar_witness R hsch hG hπ hQ hc hz,
    W.continuedScalar_gradient_zero hsch hG hπ hQ hc hz,
    W.planarWeakGradient_energy_integrable, W.continuedScalar_energy hsch hG hπ hQ hc hz⟩

 theorem continuedScalar_memW1p (harea : ExteriorCoefficientAreaTheorem)
    (hsch : PlanarSchoenflies) (hG : IsOpen d.physicalDomain)
    (hπ : Continuous π) (i : Fin m) (hQ : Continuous (Q i).quotient)
    (hc : ∀ q p, p ∈ connectedComponentIn d.physicalDomainᶜ q → π p = π q)
    (hz : ∀ᶠ p in 𝓝 (π OnePoint.infty), (Q i).quotient p = 0) :
    DeGiorgi.MemW1p 2 (fun x => R.continuedScalar hG i (complexPlaneCoordinates x)) univ := by
  obtain ⟨H, _⟩ := R.exists_continuation_witness harea hsch hG hπ i hQ hc hz
  exact H.memW1p

end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
