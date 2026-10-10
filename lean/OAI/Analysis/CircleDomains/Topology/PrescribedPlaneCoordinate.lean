import OAI.Analysis.CircleDomains.Selection.PhysicalRealCoordinate
import OAI.Analysis.CircleDomains.Rigidity.ExactTraceSobolevError

namespace OAI

/-! On a point-complement source the physical representative retains the
entire prescribed continuous sphere function, including every dust value.
The zero extension used for its derivatives does not change those values. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]

 theorem exists_prescribed_plane_coordinate
    (d : PathCodeData Sphere Sphere) (hG : IsOpen d.physicalDomain)
    (he : ∀ x : d.physicalDomain, (d.domainEquiv x).val = x.val)
    (v : EuclideanPlane → ℝ) (hv : Continuous v) (hs : HasCompactSupport v)
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) v (physicalPlaneDomain d.physicalDomain))
    (hunit : ∀ x, v x ∈ Icc 0 1)
    (hgrad : ∀ i : Fin 2, MemLp (fun x => fderiv ℝ v x (EuclideanSpace.single i 1))
      2 (volume.restrict (physicalPlaneDomain d.physicalDomain))) :
    ∃ Q : PhysicalRealCoordinate d id,
      Q.quotient = sphereFromPlaneFunction v ∧ Continuous Q.quotient ∧
      ∀ i : Fin 2, eLpNorm (fun p => fderiv ℝ Q.physical p
        (if i = 0 then (1, 0) else (0, 1))) 2
          (volume.restrict (FiniteTransfer.realChartDomain d.physicalDomain)) =
        eLpNorm (fun x => fderiv ℝ v x (EuclideanSpace.single i 1)) 2
          (volume.restrict (physicalPlaneDomain d.physicalDomain)) := by
  obtain ⟨w, hm, hws, hwe, hn, hp⟩ :=
    exists_real_physical_representative d hG id he v hsm hgrad
  have hvc : Continuous (sphereFromPlaneFunction v) := by
    apply continuousOn_univ.mp
    exact sphereFromPlaneFunction_continuousOn isOpen_univ hv.continuousOn hs.isCompact
      (fun x hx => image_eq_zero_of_notMem_tsupport hx)
  let Q : PhysicalRealCoordinate d id := {
    quotient := sphereFromPlaneFunction v
    quotient_continuous := hvc.continuousOn
    quotient_unit := fun p => sphereFromPlaneFunction_mem_Icc (G := univ)
      (fun x _ => hunit x) p (mem_univ p)
    physical := w
    physical_measurable := hm
    physical_smooth := hws
    physical_energy := hwe
    pullback := by
      intro z hz
      refine (hp z hz).trans ?_
      change quotientPlaneRepresentative d v (z : Sphere) = sphereFromPlaneFunction v z
      exact (congrArg (quotientPlaneRepresentative d v) (he ⟨(z : Sphere), hz⟩).symm).trans
        (quotientPlaneRepresentative_on_domain d v (z : Sphere) hz) }
  exact ⟨Q, rfl, hvc, hn⟩

end CircleDomainRigidity

end

end OAI
