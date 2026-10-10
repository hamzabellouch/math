import OAI.Analysis.CircleDomains.Selection.ContinuousScalarRepresentative
import OAI.Analysis.CircleDomains.Sobolev.SobolevRepresentative
import OAI.Analysis.CircleDomains.Sobolev.ScalarSobolevLimit

namespace OAI

/-! The continuous representative has the constructed planar weak gradient,
and is Sobolev on every finite-area region. -/
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

 theorem eq_continuedScalar_planar_ae (hsch : PlanarSchoenflies) (hG : IsOpen d.physicalDomain)
    (hπ : Continuous π) (hQ : Continuous (Q i).quotient)
    (hc : ∀ q p, p ∈ connectedComponentIn d.physicalDomainᶜ q → π p = π q) :
    (W.scalar ∘ complexPlaneCoordinates) =ᵐ[volume]
      (fun x => R.continuedScalar hG i (complexPlaneCoordinates x)) :=
  complexPlaneCoordinates_measurePreserving.quasiMeasurePreserving.ae
    (W.eq_continuedScalar_ae R hsch hG hπ hQ hc)

include W in
 theorem continuedScalar_memW1p_on (hsch : PlanarSchoenflies) (hG : IsOpen d.physicalDomain)
    (hπ : Continuous π) (hQ : Continuous (Q i).quotient)
    (hc : ∀ q p, p ∈ connectedComponentIn d.physicalDomainᶜ q → π p = π q)
    {U : Set ℂ} (hU : MeasurableSet U) (hfinite : volume U ≠ ∞) :
    DeGiorgi.MemW1p 2 (fun x => R.continuedScalar hG i (complexPlaneCoordinates x))
      (complexPlaneCoordinates ⁻¹' U) :=
  DeGiorgi.MemW1p.congr_ae (memW1p_on W hU hfinite)
    (ae_restrict_of_ae (W.eq_continuedScalar_planar_ae hsch hG hπ hQ hc))

 theorem continuedScalar_weak (hsch : PlanarSchoenflies) (hG : IsOpen d.physicalDomain)
    (hπ : Continuous π) (hQ : Continuous (Q i).quotient)
    (hc : ∀ q p, p ∈ connectedComponentIn d.physicalDomainᶜ q → π p = π q) :
    DeGiorgi.HasWeakGrad W.planarWeakGradient
      (fun x => R.continuedScalar hG i (complexPlaneCoordinates x)) univ := by
  intro j
  apply (W.boundedRepresentative_weak j).congr_ae
  · apply ae_restrict_of_ae
    exact W.boundedRepresentative_ae.trans (W.eq_continuedScalar_planar_ae hsch hG hπ hQ hc)
  · exact Filter.EventuallyEq.rfl

end ScalarWeakLimit
end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
