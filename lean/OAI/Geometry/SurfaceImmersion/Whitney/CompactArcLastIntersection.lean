import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.ContinuousOn

namespace OAI

/-! The last intersection of a compact curve with a closed set leaves a
terminal arc disjoint from that set. No finiteness of intersections is assumed. -/
noncomputable section
open Set
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X : Type*} [TopologicalSpace X]

theorem compact_curve_last_intersection {δ : ℝ → X} {c d : ℝ} {K : Set X}
    (hcd : c ≤ d) (hδ : ContinuousOn δ (Icc c d)) (hK : IsClosed K)
    (hc : δ c ∈ K) (hd : δ d ∉ K) :
    ∃ m ∈ Ico c d, δ m ∈ K ∧ ∀ t ∈ Ioc m d, δ t ∉ K := by
  let A : Set (Icc c d) := (fun t => δ t.val) ⁻¹' K
  have hA : IsCompact A := (hK.preimage hδ.domRestrict).isCompact
  have hne : A.Nonempty := ⟨⟨c,left_mem_Icc.mpr hcd⟩,hc⟩
  obtain ⟨m,hm,hmax⟩ := hA.exists_isGreatest hne
  have hmd : m.val < d := by
    refine lt_of_le_of_ne m.property.2 ?_
    intro he
    apply hd
    simpa only [A,mem_preimage,he] using hm
  refine ⟨m.val,⟨m.property.1,hmd⟩,hm,?_⟩
  intro t ht htK
  have htcd : t ∈ Icc c d := ⟨m.property.1.trans ht.1.le,ht.2⟩
  have htm : (⟨t,htcd⟩ : Icc c d) ≤ m := hmax htK
  exact (not_le_of_gt ht.1) htm

theorem compact_arc_last_intersection [T2Space X] {γ δ : ℝ → X} {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) (hγ : ContinuousOn γ (Icc a b))
    (hδ : ContinuousOn δ (Icc c d)) (hjoin : δ c = γ b)
    (hend : δ d ∉ γ '' Icc a b) :
    ∃ s ∈ Icc a b, ∃ m ∈ Ico c d, γ s = δ m ∧
      ∀ u ∈ Icc a s, ∀ v ∈ Ioc m d, γ u ≠ δ v := by
  obtain ⟨m,hm,hmK,htail⟩ := compact_curve_last_intersection hcd hδ
    (isCompact_Icc.image_of_continuousOn hγ).isClosed
    (hjoin ▸ mem_image_of_mem γ (right_mem_Icc.mpr hab)) hend
  obtain ⟨s,hs,hsm⟩ := hmK
  refine ⟨s,hs,m,hm,hsm,?_⟩
  intro u hu v hv huv
  apply htail v hv
  exact ⟨u,⟨hu.1,hu.2.trans hs.2⟩,huv⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
