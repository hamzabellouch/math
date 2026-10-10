import OAI.Analysis.CircleDomains.Transfer.ContinuousSourceProjection
import OAI.Analysis.CircleDomains.Selection.ScalarEndIdentification

namespace OAI

/-! The actual weak scalar has a continuous representative on the sphere.
The representative uses the source quotient on every matched end. -/
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

 def continuedScalar (hG : IsOpen d.physicalDomain) (i : Fin m) : Sphere → ℝ :=
  (Q i).quotient ∘ R.limit.sourceProjection hG π

 theorem continuedScalar_continuous (hG : IsOpen d.physicalDomain)
    (hπ : Continuous π) (i : Fin m) (hQ : Continuous (Q i).quotient)
    (hc : ∀ q p, p ∈ connectedComponentIn d.physicalDomainᶜ q → π p = π q) :
    Continuous (R.continuedScalar hG i) :=
  hQ.comp (R.limit.sourceProjection_continuous hG π hπ hc)

 theorem continuedScalar_unit (hG : IsOpen d.physicalDomain) (i : Fin m) (p : Sphere) :
    R.continuedScalar hG i p ∈ Icc 0 1 := (Q i).quotient_unit _

 theorem continuedScalar_on_image (hG : IsOpen d.physicalDomain) (i : Fin m)
    {x : Sphere} (hx : x ∈ d.physicalDomain) :
    R.continuedScalar hG i (extendAtInfinity R.limit.function x) = (Q i).quotient (π x) := by
  unfold continuedScalar
  simp only [comp_apply, R.limit.sourceProjection_on_image hG π hx]

 theorem continuedScalar_eq_imageScalar (hG : IsOpen d.physicalDomain) (i : Fin m)
    {z : ℂ} (hz : z ∈ R.limit.function '' (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain)) :
    R.continuedScalar hG i z = R.imageScalar i z := by
  obtain ⟨x, hx, rfl⟩ := hz
  rw [R.imageScalar_apply hG i hx, (Q i).pullback x hx]
  exact R.continuedScalar_on_image hG i hx

 theorem ScalarWeakLimit.eq_continuedScalar_ae {i : Fin m} (W : R.ScalarWeakLimit i)
    (hsch : PlanarSchoenflies) (hG : IsOpen d.physicalDomain)
    (hπ : Continuous π) (hQ : Continuous (Q i).quotient)
    (hc : ∀ q p, p ∈ connectedComponentIn d.physicalDomainᶜ q → π p = π q) :
    ∀ᵐ z ∂(volume : Measure ℂ), W.scalar z = R.continuedScalar hG i z := by
  filter_upwards [W.eq_source_ae R hsch hG,
    W.eq_on_all_matched_ends hsch hG hπ hQ hc] with z hz hends
  by_cases him : z ∈ R.limit.function '' (((↑) : ℂ → Sphere) ⁻¹' d.physicalDomain)
  · exact (hz him).trans (R.continuedScalar_eq_imageScalar hG i him).symm
  · have hout : (z : Sphere) ∉ extendAtInfinity R.limit.function '' d.physicalDomain := by
      rintro ⟨p, hp, he⟩
      cases p using OnePoint.rec with
      | infty => exact OnePoint.coe_ne_infty z (by simpa using he.symm)
      | coe x =>
        exact him ⟨x, hp, OnePoint.coe_injective (by simpa only [extendAtInfinity_coe] using he)⟩
    let A := R.limit.chosenSourceEnd hG (z : Sphere) hout
    have hzin : z ∈ A.matching.plane := by
      change (z : Sphere) ∈ connectedComponentIn
        (extendAtInfinity R.limit.function '' d.physicalDomain)ᶜ A.matching.point
      exact (congrArg (fun p : Sphere => p ∈ connectedComponentIn
        (extendAtInfinity R.limit.function '' d.physicalDomain)ᶜ A.matching.point)
        A.point_eq).mp (mem_connectedComponentIn A.matching.outside)
    rw [hends A.source A.matching hzin]
    unfold continuedScalar
    simp only [comp_apply, R.limit.sourceProjection_off_image hG π hout]
    rfl

end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
