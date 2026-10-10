import OAI.GroupTheory.PolycyclicRecognition.Geometry.GradedFlowLimit
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UrysohnsLemma

namespace OAI

/-! # One compact neighborhood for all sufficiently large coordinate flows -/

namespace PolycyclicRecognition

open Set Filter Metric
open scoped Topology

/-- Compact convergence of coordinate paths allows one compact cutoff to
contain the entire late family inside the prescribed open chart. -/
theorem exists_compact_eventual_flow_image
    {X Y ι : Type*} [TopologicalSpace X] [MetricSpace Y] [LocallyCompactSpace Y]
    {l : Filter ι} {F : ι → X → Y} {f : X → Y} {K : Set X} {U : Set Y}
    (hK : IsCompact K) (hf : ContinuousOn f K) (hU : IsOpen U)
    (himage : f '' K ⊆ U) (hF : TendstoUniformlyOn F f l K) :
    ∃ Q : Set Y, IsCompact Q ∧ Q ⊆ U ∧ f '' K ⊆ Q ∧
      ∀ᶠ i in l, F i '' K ⊆ Q := by
  have hc : IsCompact (f '' K) := hK.image_of_continuousOn hf
  obtain ⟨O, hO, hfO, hOU, hOc⟩ := exists_open_between_and_isCompact_closure hc hU himage
  obtain ⟨δ, hδ, hthick⟩ := hc.exists_thickening_subset_open hO hfO
  refine ⟨closure O, hOc, hOU, hfO.trans subset_closure, ?_⟩
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hF) δ hδ] with i hi
  rintro y ⟨x, hx, rfl⟩
  apply subset_closure
  apply hthick
  exact mem_thickening_iff.mpr ⟨f x, mem_image_of_mem f hx, by simpa only [dist_comm] using hi x hx⟩

end PolycyclicRecognition

end OAI
