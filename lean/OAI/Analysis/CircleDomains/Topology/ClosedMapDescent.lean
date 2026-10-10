import OAI.Analysis.CircleDomains.Selection.PointFiberConcentration

namespace OAI

/-! A continuous scalar constant on each compact fiber descends through
a closed quotient. Only continuity along the relevant fiber is needed. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem closed_map_section_continuousAt_of_fiber
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {P : X → Y} (hP : IsClosedMap P) (s : Y → X) (hs : ∀ y, P (s y) = y)
    {a : X → ℝ} {q : Y} {v : ℝ}
    (ha : ∀ z, P z = q → ContinuousAt a z)
    (hc : ∀ z, P z = q → a z = v) :
    ContinuousAt (a ∘ s) q ∧ a (s q) = v := by
  have hvalue : a (s q) = v := hc _ (hs q)
  refine ⟨?_, hvalue⟩
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  let U := interior (a ⁻¹' ball v ε)
  have hU : IsOpen U := isOpen_interior
  have hfiber : P ⁻¹' {q} ⊆ U := by
    intro z hz
    apply mem_interior_iff_mem_nhds.mpr
    have hn : ball v ε ∈ 𝓝 (a z) := by rw [hc z hz]; exact ball_mem_nhds _ hε
    exact (ha z hz).preimage_mem_nhds hn
  have hV : IsOpen (kernImage P U) := isClosedMap_iff_kernImage.mp hP hU
  have hqV : q ∈ kernImage P U := fun _ hz => hfiber hz
  filter_upwards [hV.mem_nhds hqV] with y hy
  have hsy : s y ∈ U := hy (hs y)
  have hnear := interior_subset hsy
  simpa only [mem_preimage, mem_ball, comp_apply, hvalue] using hnear

end CircleDomainRigidity

end

end OAI
