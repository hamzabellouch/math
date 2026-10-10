import Mathlib

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
open scoped NNReal

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology
open MeasureTheory
open scoped ContDiff ENNReal

open Set Filter Manifold Bundle ContinuousLinearMap MeasureTheory
open scoped Topology ContDiff Manifold Bundle ENNReal

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology Manifold

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Bundle
open scoped Topology Bundle

open scoped Topology
open Function Manifold Set
open Manifold Bundle
open scoped Manifold Bundle
open Set

open Set Filter
open scoped Topology ContDiff

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

namespace WeakMTWTransport

lemma interior_of_compact_unique_fiber {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space Y] {f : X → Y} {C : Set X} {x : X}
    (hC : IsCompact C) (hf : Continuous f)
    (hs : ∀ y, ∃ q ∈ C, f q = y)
    (hu : ∀ q ∈ C, f q = f x → q = x)
    (hi : ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ InjOn f U) : x ∈ interior C := by
  obtain ⟨U,hU,hxU,hUinj⟩ := hi
  have hclosed : IsClosed (f '' (C \ U)) := ((hC.diff hU).image hf).isClosed
  have hxnot : f x ∉ f '' (C \ U) := by
    rintro ⟨q,hq,hqx⟩
    exact hq.2 (hu q hq.1 hqx ▸ hxU)
  apply mem_interior_iff_mem_nhds.mpr
  filter_upwards [hU.mem_nhds hxU,
    hf.continuousAt.preimage_mem_nhds (hclosed.isOpen_compl.mem_nhds hxnot)] with v hv hvf
  obtain ⟨q,hq,hqv⟩ := hs (f v)
  have hqU : q ∈ U := by
    by_contra hqU
    exact hvf ⟨q,⟨hq,hqU⟩,hqv⟩
  exact hUinj hqU hv hqv ▸ hq

end WeakMTWTransport

end

end OAI
