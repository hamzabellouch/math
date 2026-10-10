import OAI.Probability.SLE.Geometry.ArcRealRetraction

namespace OAI

/-! Every point of the half-plane outside a simple attached arc lies in
an unbounded complementary component. -/
noncomputable section
open Set Filter Function
open scoped Topology

namespace SLEExactGauge

theorem simple_arc_halfPlane_component_unbounded
    (p : C(unitInterval,ℂ)) (hi : Injective p) (h0 : p 0=0)
    (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane)
    {z : ℂ} (hz : z ∈ upperHalfPlane \ range p) :
    ¬ Bornology.IsBounded (connectedComponentIn (upperHalfPlane \ range p) z) := by
  let K : Set ℂ := range p ∪ {w : ℂ | w.im=0}
  have hK : IsClosed K := (p.continuous.isClosedEmbedding hi).isClosed_range.union
    (isClosed_eq Complex.continuous_im continuous_const)
  obtain ⟨r,hrK,hrfix⟩ := simple_arc_real_retraction p hi h0 hH
  have hzK : z ∉ K := by
    rintro (h | h)
    · exact hz.2 h
    · exact hz.1.ne' h
  have hn := retract_complement_component_unbounded hK r r.continuous hrK hrfix hzK
  have hsub : connectedComponentIn Kᶜ z ⊆ upperHalfPlane \ range p := by
    intro w hw
    have hwK := connectedComponentIn_subset Kᶜ z hw
    have him : 0 < w.im := by
      by_contra hh
      have hnonpos : w.im ≤ 0 := le_of_not_gt hh
      obtain ⟨v,hv,hvim⟩ := isPreconnected_connectedComponentIn.intermediate_value
        hw (mem_connectedComponentIn hzK) Complex.continuous_im.continuousOn
        (show (0 : ℝ) ∈ Icc w.im z.im from ⟨hnonpos,hz.1.le⟩)
      exact connectedComponentIn_subset Kᶜ z hv (Or.inr hvim)
    exact ⟨him,fun h => hwK (Or.inl h)⟩
  have hcc : connectedComponentIn Kᶜ z ⊆
      connectedComponentIn (upperHalfPlane \ range p) z :=
    isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn hzK) hsub
  exact fun hb => hn (hb.subset hcc)

end SLEExactGauge

end

end OAI
