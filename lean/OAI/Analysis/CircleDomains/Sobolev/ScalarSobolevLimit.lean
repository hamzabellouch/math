import OAI.Analysis.CircleDomains.Sobolev.ScalarLocalLp
import OAI.Analysis.CircleDomains.Sobolev.ComplexSobolevTransport

namespace OAI

/-! The constructed scalar limit is Sobolev on every planar region of
finite area, including across the finite-model holes. -/
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

 theorem memW1p_on {U : Set ℂ} (hU : MeasurableSet U) (hfinite : volume U ≠ ∞) :
    DeGiorgi.MemW1p 2 (W.scalar ∘ complexPlaneCoordinates) (complexPlaneCoordinates ⁻¹' U) := by
  have hm := complexPlaneCoordinates_measurePreserving.restrict_preimage hU
  refine ⟨(W.scalar_memLp_on hfinite).comp_measurePreserving hm, ?_⟩
  intro j
  fin_cases j
  · refine ⟨W.horizontal ∘ complexPlaneCoordinates,
      ((Lp.memLp W.horizontal).restrict U).comp_measurePreserving hm, ?_⟩
    exact weakPartial_of_complex_identity 0 1 complexPlaneCoordinates_zero
      (fun φ hφ hs => (W.derivative φ hφ hs).1) U
  · refine ⟨W.vertical ∘ complexPlaneCoordinates,
      ((Lp.memLp W.vertical).restrict U).comp_measurePreserving hm, ?_⟩
    exact weakPartial_of_complex_identity 1 Complex.I complexPlaneCoordinates_one
      (fun φ hφ hs => (W.derivative φ hφ hs).2) U

end ScalarWeakLimit
end RetainedRealCircleModel
end CircleDomainRigidity

end

end OAI
