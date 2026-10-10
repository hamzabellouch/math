import OAI.Analysis.CircleDomains.Rigidity.MeanMaskedPhysicalData
import OAI.Analysis.CircleDomains.Selection.MarkedPhysicalBranches

namespace OAI

/-! The individual coordinate data consumed by a finite mixed transfer.
These fields retain the actual level graph and its chosen marked branches. -/

open Set Function Filter MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

structure MaskedCoordinateData {T : Type*} (G U : Set Sphere)
    (π : Sphere → Sphere) (σ : T → Sphere) where
  graph : Set (Sphere × UnitAddCircle)
  graph_closed : IsClosed graph
  mask : Set Sphere
  mask_closed : IsClosed mask
  mask_frontier : frontier mask ⊆ U
  singular : T
  Index : Type
  patch : Index → Set Sphere
  patch_open : ∀ i, IsOpen (patch i)
  cover : mask \ {σ singular} ⊆ ⋃ i, patch i
  branch : Index → Sphere → ℝ
  bound : Index → ℝ
  branch_bounded : ∀ i x, |branch i x| ≤ bound i
  physical : (ℝ × ℝ) → UnitAddCircle
  measurable : Measurable physical
  gradient_measurable : Measurable (circleGradient physical)
  smooth : SmoothCircleOn physical (realChartDomain G ∩ interior (physicalMask π mask))
  energy : MemLp (circleGradient physical) 2
    ((volume.restrict (realChartDomain G)).restrict (physicalMask π mask))
  physical_graph : ∀ x ∈ realChartDomain G ∩ interior (physicalMask π mask),
    (π (Complex.equivRealProdCLM.symm x : Sphere), physical x) ∈ graph
  branch_smooth : ∀ i, ContDiffOn ℝ ∞
    (fun x : ℝ × ℝ => branch i (π (Complex.equivRealProdCLM.symm x : Sphere)))
    (realChartDomain G ∩ realChartDomain (π ⁻¹' patch i))
  branch_projection : ∀ i x, x ∈ realChartDomain G ∩ realChartDomain (π ⁻¹' patch i) →
    (branch i (π (Complex.equivRealProdCLM.symm x : Sphere)) : UnitAddCircle) = physical x
  lower : T → ℝ
  upper : T → ℝ
  width_nonneg : ∀ s, 0 ≤ upper s - lower s
  width_summable : Summable (fun s => (upper s - lower s) ^ 2)
  marked_fiber : ∀ s, {t : UnitAddCircle | (σ s, t) ∈ graph} ⊆
    ((↑) : ℝ → UnitAddCircle) '' Icc (lower s) (upper s)
  marked_branch : ∀ s, σ s ∈ mask → σ s ≠ σ singular → ∃ i,
    σ s ∈ patch i ∧ lower s = liminf (branch i) (𝓝[U] (σ s)) ∧
      upper s = limsup (branch i) (𝓝[U] (σ s))
  free_fiber : ∀ x ∈ π '' Gᶜ, x ∉ range σ → {t : UnitAddCircle | (x, t) ∈ graph}.Subsingleton

end CircleDomainRigidity.FiniteTransfer

end

end OAI
