import OAI.Analysis.CircleDomains.Sobolev.ContinuousScalarSobolev
import OAI.Analysis.CircleDomains.Rigidity.MatchedSourceProjection

namespace OAI

/-! Scalar tests vanishing near the source end at infinity continue with
compact planar support. Their global planar Sobolev witness has the actual
weak fields, which vanish off the limiting domain. -/
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

 theorem continuedScalar_on_end (hG : IsOpen d.physicalDomain) (i : Fin m)
    (hc : ∀ q p, p ∈ connectedComponentIn d.physicalDomainᶜ q → π p = π q)
    {q p : Sphere} (E : RealTargetEnd R.limit q)
    (hp : p ∈ connectedComponentIn
      (extendAtInfinity R.limit.function '' d.physicalDomain)ᶜ E.point) :
    R.continuedScalar hG i p = (Q i).quotient (π q) :=
  congrArg (Q i).quotient (E.sourceProjection_eq hG π hc hp)

 theorem continuedScalar_zero_near_infty (hG : IsOpen d.physicalDomain)
    (hπ : Continuous π) (i : Fin m)
    (hc : ∀ q p, p ∈ connectedComponentIn d.physicalDomainᶜ q → π p = π q)
    (hz : ∀ᶠ p in 𝓝 (π OnePoint.infty), (Q i).quotient p = 0) :
    ∀ᶠ p in 𝓝 (OnePoint.infty : Sphere), R.continuedScalar hG i p = 0 := by
  have hinf : OnePoint.infty ∈ d.physicalDomain :=
    R.model.core_source 0 (R.model.plane_core 0 (Or.inr rfl))
  have hp : R.limit.sourceProjection hG π OnePoint.infty = π OnePoint.infty :=
    R.limit.sourceProjection_on_image hG π hinf
  have ht := (R.limit.sourceProjection_continuous hG π hπ hc).tendsto OnePoint.infty
  rw [hp] at ht
  exact ht.eventually hz

 theorem continuedScalar_hasCompactSupport (hG : IsOpen d.physicalDomain)
    (hπ : Continuous π) (i : Fin m)
    (hc : ∀ q p, p ∈ connectedComponentIn d.physicalDomainᶜ q → π p = π q)
    (hz : ∀ᶠ p in 𝓝 (π OnePoint.infty), (Q i).quotient p = 0) :
    HasCompactSupport (fun z : ℂ => R.continuedScalar hG i z) := by
  rw [hasCompactSupport_iff_eventuallyEq]
  have ht : Tendsto ((↑) : ℂ → Sphere) (coclosedCompact ℂ) (𝓝 OnePoint.infty) :=
    OnePoint.tendsto_coe_infty
  exact ht.eventually (R.continuedScalar_zero_near_infty hG hπ i hc hz)

 def ScalarWeakLimit.continuedScalar_witness {i : Fin m} (W : R.ScalarWeakLimit i)
    (hsch : PlanarSchoenflies) (hG : IsOpen d.physicalDomain)
    (hπ : Continuous π) (hQ : Continuous (Q i).quotient)
    (hc : ∀ q p, p ∈ connectedComponentIn d.physicalDomainᶜ q → π p = π q)
    (hz : ∀ᶠ p in 𝓝 (π OnePoint.infty), (Q i).quotient p = 0) :
    DeGiorgi.MemW1pWitness 2
      (fun x => R.continuedScalar hG i (complexPlaneCoordinates x)) univ where
  memLp := by
    rw [Measure.restrict_univ]
    exact ((R.continuedScalar_continuous hG hπ i hQ hc).comp
      (OnePoint.continuous_coe.comp complexPlaneCoordinates.continuous)).memLp_of_hasCompactSupport
        ((R.continuedScalar_hasCompactSupport hG hπ i hc hz).comp_homeomorph
          complexPlaneCoordinates.toHomeomorph)
  weakGrad := W.planarWeakGradient
  weakGrad_component_memLp j := by
    simpa only [Measure.restrict_univ] using W.planarWeakGradient_memLp j
  isWeakGrad := W.continuedScalar_weak hsch hG hπ hQ hc

end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
