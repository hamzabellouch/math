import OAI.Analysis.CircleDomains.Sobolev.SobolevConformalTransport
import OAI.Analysis.CircleDomains.Rigidity.ZeroTraceEnergy

namespace OAI

/-! A transported continuous zero-trace error extends to the whole target
plane, with no added complementary energy. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

 theorem zero_trace_conformal_transport
    {f fi : Sphere → Sphere} {U V : Set Sphere}
    (heq : IsSmoothSphereEquivalence f fi U V) (hU : IsOpen U) (hV : IsOpen V)
    (hinf : OnePoint.infty ∈ U) (hfix : f OnePoint.infty = OnePoint.infty)
    (hf : IsConformalOn f U) {u v : EuclideanPlane → ℝ}
    (hu : Continuous u) (hs : HasCompactSupport u)
    (H : DeGiorgi.MemW1pWitness 2 u univ)
    (hv : EqOn v (planeInverseTransport fi u) (physicalPlaneDomain V))
    (hvc : Continuous v) (hvs : HasCompactSupport v)
    (hz : ∀ x ∉ physicalPlaneDomain V, v x = 0) :
    ∃ K : DeGiorgi.MemW1pWitness 2 v univ,
      (∀ i : Fin 2, ∀ x ∉ physicalPlaneDomain V, K.weakGrad x i = 0) ∧
      (∫ x, K.weakGrad x 0 ^ 2 + K.weakGrad x 1 ^ 2) ≤
        ∫ x in physicalPlaneDomain U, H.weakGrad x 0 ^ 2 + H.weakGrad x 1 ^ 2 := by
  obtain ⟨W, hW⟩ := sobolev_conformal_transport heq hU hV hinf hfix hf hu hs H hv
    ((hvc.memLp_of_hasCompactSupport hvs).restrict _)
  let K := zeroTraceWitness (isOpen_physicalPlaneDomain hV) hvc hvs hz W
  exact ⟨K, zeroTraceWitness_zero (isOpen_physicalPlaneDomain hV) hvc hvs hz W,
    (zeroTraceWitness_energy (isOpen_physicalPlaneDomain hV) hvc hvs hz W).trans_le hW⟩

end CircleDomainRigidity

end

end OAI
