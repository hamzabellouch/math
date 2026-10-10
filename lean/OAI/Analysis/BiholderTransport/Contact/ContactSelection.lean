import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.MetricDefinitions

namespace OAI

section
section
noncomputable section
open Set Filter Manifold MeasureTheory Bundle Metric
open scoped Topology ContDiff ENNReal NNReal

namespace WeakMTWTransport
section ContactSelection
variable {M : Type*} [MetricSpace M] [CompactSpace M]

lemma contact_selection_continuousAt {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v)
    {T : M → M} (hT : ∀ z, contactGap u v z (T z)=0) {x : M}
    (hx : ∀ y, contactGap u v x y=0 → y=T x) : ContinuousAt T x := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  let A := {z : M×M | contactGap u v z.1 z.2=0 ∧ z.2∉ball (T x) ε}
  have hg : Continuous (fun z : M×M => contactGap u v z.1 z.2) :=
    ((hu.comp continuous_fst).add
      (((continuous_fst.dist continuous_snd).pow 2).div_const 2)).add
      (hv.comp continuous_snd)
  have hA : IsClosed A := (isClosed_eq hg continuous_const).inter
    (isOpen_ball.preimage continuous_snd).isClosed_compl
  have hB : IsClosed (Prod.fst '' A) := isClosedMap_fst_of_compactSpace A hA
  have hxB : x∉Prod.fst '' A := by
    rintro ⟨⟨z,y⟩,⟨hzy,hy⟩,rfl⟩
    exact hy ((hx y hzy) ▸ mem_ball_self hε)
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (hB.isOpen_compl.mem_nhds hxB)
  refine ⟨δ,hδ,fun {z} hz => ?_⟩
  by_contra hbad
  exact hball hz ⟨(z,T z),⟨hT z,hbad⟩,rfl⟩

variable [Nonempty M]
def contactSelection {v : M → ℝ} (hv : Continuous v) (x : M) : M :=
  (cTransform_gap_zero hv x).choose

lemma contactSelection_mem {v : M → ℝ} (hv : Continuous v) (x : M) :
    contactGap (cTransform v) v x (contactSelection hv x)=0 :=
  (cTransform_gap_zero hv x).choose_spec

end ContactSelection

end WeakMTWTransport
end
end
end

end OAI
