import OAI.Analysis.CircleDomains.Sobolev.FilledScalarSliceDerivative
import OAI.Analysis.CircleDomains.Topology.SphereClusterBridge

namespace OAI

/-! The fixed-line hypotheses of the disk jump estimate for the actual
finite scalar model, including its original terminal cluster bounds. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)]
namespace RetainedRealCircleModel.HoleFilling
variable {d : PathCodeData Sphere Sphere} {π : Sphere → Sphere} {m : ℕ}
  {Q : Fin m → PhysicalRealCoordinate d π} {R : RetainedRealCircleModel d π Q}
  {i : Fin m} {n : ℕ} (F : R.HoleFilling i n)

 theorem line_domain (y : ℝ) : diskLineDomain F.center F.radius y =
    horizontalLine y ⁻¹' (((↑) : ℂ → Sphere) ⁻¹' (R.model.stages n).domain) := by
  rw [F.complement]
  rfl

 theorem transferred_line_contDiffOn (y : ℝ) :
    ContDiffOn ℝ 1 (R.transferred i n ∘ horizontalLine y)
      (diskLineDomain F.center F.radius y) := by
  rw [F.line_domain]
  exact ((R.transferred_contDiffOn i n).of_le (by simp)).comp
    (contDiff_horizontalLine y).contDiffOn (fun _ hx => hx)

 theorem filled_line_eq (y : ℝ) :
    EqOn (F.filled ∘ horizontalLine y) (clipScalar ∘ (R.transferred i n ∘ horizontalLine y))
      (diskLineDomain F.center F.radius y) := by
  intro x hx
  apply F.filled_on_domain
  rw [F.line_domain] at hx
  exact hx

 theorem line_cluster_error (y : ℝ) (s : (R.model.stages n).indices) {x t : ℝ}
    (hx : horizontalLine y x ∈ closedBall (F.center s) (F.radius s))
    (ht : MapClusterPt t (𝓝[diskLineDomain F.center F.radius y] x)
      (R.transferred i n ∘ horizontalLine y)) :
    |t - F.value s| ≤ terminalOscillation ((R.model.stages n).terminals.H s)
      ((R.model.stages n).functions (prefixIndex (R.index i) n)) := by
  apply F.cluster_error s t
  apply planar_mapClusterPt_mem_componentClusterValues
  · rw [F.component]
    exact mem_image_of_mem _ hx
  · apply horizontal_cluster_is_planar
    simpa only [F.line_domain, RetainedRealCircleModel.transferred] using ht

end RetainedRealCircleModel.HoleFilling
end CircleDomainRigidity

end

end OAI
