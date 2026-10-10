import OAI.Analysis.CircleDomains.Selection.RealPhysicalRepresentative
import OAI.Analysis.CircleDomains.Topology.PlaneRepresentativeBounds
import OAI.Analysis.CircleDomains.Topology.SpherePlaneContinuity

namespace OAI

/-! A genuine continuous quotient coordinate with its smooth finite-energy
physical representative, ready for finite transfer. -/

open Set Function MeasureTheory
open scoped ENNReal Topology
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable {X : Type*} [MetricSpace X] [MeasurableSpace C(PathTime, X)]

structure PhysicalRealCoordinate (d : PathCodeData X Sphere) (π : Sphere → X) where
  quotient : X → ℝ
  quotient_continuous : ContinuousOn quotient d.quotientDomain
  quotient_unit : ∀x, quotient x ∈ Icc 0 1
  physical : (ℝ × ℝ) → ℝ
  physical_measurable : Measurable physical
  physical_smooth : ContDiffOn ℝ (⊤ : ℕ∞) physical (FiniteTransfer.realChartDomain d.physicalDomain)
  physical_energy : MemLp (FiniteTransfer.planarGradient physical) 2
    (volume.restrict (FiniteTransfer.realChartDomain d.physicalDomain))
  pullback : ∀z : ℂ, (z : Sphere) ∈ d.physicalDomain → physical (Complex.equivRealProdCLM z) = quotient (π z)

theorem physicalRealCoordinate_of_plane_smoothing
    (d : PathCodeData X Sphere) (hG : IsOpen d.physicalDomain)
    (π : Sphere → X) (he : ∀x : d.physicalDomain, (d.domainEquiv x).val = π x.val)
    (w : EuclideanPlane → ℝ) (hw : ContDiffOn ℝ (⊤ : ℕ∞) w (physicalPlaneDomain d.physicalDomain))
    (hunit : ∀x ∈ physicalPlaneDomain d.physicalDomain, w x ∈ Icc 0 1)
    (henergy : ∀i : Fin 2, MemLp (fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1))
      2 (volume.restrict (physicalPlaneDomain d.physicalDomain)))
    {K : Set EuclideanPlane} (hK : IsCompact K) (hzero : ∀x ∉ K, w x = 0) :
    ∃Q : PhysicalRealCoordinate d π, Q.quotient = quotientPlaneRepresentative d w ∧
      ∀i : Fin 2, eLpNorm (fun p => (fderiv ℝ Q.physical p)
        (if i = 0 then (1, 0) else (0, 1))) 2
          (volume.restrict (FiniteTransfer.realChartDomain d.physicalDomain)) =
        eLpNorm (fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1)) 2
          (volume.restrict (physicalPlaneDomain d.physicalDomain)) := by
  obtain ⟨v, hm, hs, hew, hnorm, hp⟩ := exists_real_physical_representative d hG π he w hw henergy
  refine ⟨{
    quotient := quotientPlaneRepresentative d w
    quotient_continuous := quotientPlaneRepresentative_continuousOn d w
      (sphereFromPlaneFunction_continuousOn hG hw.continuousOn hK hzero)
    quotient_unit := quotientPlaneRepresentative_mem_Icc d hunit
    physical := v
    physical_measurable := hm
    physical_smooth := hs
    physical_energy := hew
    pullback := hp }, rfl, hnorm⟩

end CircleDomainRigidity

end

end OAI
