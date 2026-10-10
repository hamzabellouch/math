import OAI.Geometry.SurfaceImmersion.Whitney.RegularPathCornerChart

namespace OAI

/-! Embeddedness forces strict separation of the two returning graph branches. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {p q : M} {γ : Path p q} {t : ℝ}
namespace RegularPathCornerChart

lemma left_graph_realized (C : RegularPathCornerChart γ t) {x : ℝ}
    (hx : x ∈ C.leftParameter '' Icc C.lower t) :
    ![x,C.leftGraph x] ∈ C.chart.target ∧
      C.chart.symm ![x,C.leftGraph x] = γ.extend (C.leftParameter.symm x) := by
  obtain ⟨u,hu,rfl⟩ := hx
  have h := C.left_chart u hu
  refine ⟨h.2 ▸ C.chart.map_source h.1,?_⟩
  rw [C.leftParameter.symm_apply_apply,← h.2,C.chart.left_inv h.1]

lemma right_graph_realized (C : RegularPathCornerChart γ t) {x : ℝ}
    (hx : x ∈ C.rightParameter '' Icc t C.upper) :
    ![x,C.rightGraph x] ∈ C.chart.target ∧
      C.chart.symm ![x,C.rightGraph x] = γ.extend (C.rightParameter.symm x) := by
  obtain ⟨u,hu,rfl⟩ := hx
  have h := C.right_chart u hu
  refine ⟨h.2 ▸ C.chart.map_source h.1,?_⟩
  rw [C.rightParameter.symm_apply_apply,← h.2,C.chart.left_inv h.1]

lemma branch_graphs_ne (C : RegularPathCornerChart γ t) (hi : Function.Injective γ)
    {u v : ℝ} (hu : u ∈ Ico C.lower t) (hv : v ∈ Ioc t C.upper) :
    ![C.leftParameter u,C.leftGraph (C.leftParameter u)] ≠
      ![C.rightParameter v,C.rightGraph (C.rightParameter v)] := by
  intro he
  have hl := C.left_chart u ⟨hu.1,hu.2.le⟩
  have hr := C.right_chart v ⟨hv.1.le,hv.2⟩
  have hp : γ.extend u = γ.extend v := C.chart.injOn hl.1 hr.1 (hl.2.trans (he.trans hr.2.symm))
  have hu01 : u ∈ Icc (0:ℝ) 1 :=
    ⟨C.lower_pos.le.trans hu.1,hu.2.le.trans (C.lt_upper.trans C.upper_lt_one).le⟩
  have hv01 : v ∈ Icc (0:ℝ) 1 :=
    ⟨(C.lower_pos.trans C.lower_lt).le.trans hv.1.le,hv.2.trans C.upper_lt_one.le⟩
  rw [Path.extend_apply γ hu01,Path.extend_apply γ hv01] at hp
  have huv := congrArg (fun z : I => (z:ℝ)) (hi hp)
  exact (hu.2.trans hv.1).ne huv

lemma graphs_ne_on_overlap (C : RegularPathCornerChart γ t) (hi : Function.Injective γ)
    {x : ℝ} (hx : x ∈ C.leftParameter '' Ico C.lower t)
    (hx' : x ∈ C.rightParameter '' Ioc t C.upper) : C.leftGraph x ≠ C.rightGraph x := by
  obtain ⟨u,hu,he⟩ := hx
  obtain ⟨v,hv,he'⟩ := hx'
  intro hg
  apply C.branch_graphs_ne hi hu hv
  rw [he,he',hg]

lemma graphs_ordered_on_interval (C : RegularPathCornerChart γ t)
    (hi : Function.Injective γ) {a b : ℝ}
    (hleft : Ioo a b ⊆ C.leftParameter '' Ico C.lower t)
    (hright : Ioo a b ⊆ C.rightParameter '' Ioc t C.upper) :
    (∀ x ∈ Ioo a b, C.leftGraph x < C.rightGraph x) ∨
      (∀ x ∈ Ioo a b, C.rightGraph x < C.leftGraph x) := by
  have hn : ∀ x ∈ Ioo a b, C.rightGraph x - C.leftGraph x ≠ 0 := by
    intro x hx
    exact sub_ne_zero.mpr (C.graphs_ne_on_overlap hi (hleft hx) (hright hx)).symm
  have hs := isPreconnected_Ioo.mapsTo_Ioi_or_Iio
    (C.right_smooth.continuous.sub C.left_smooth.continuous).continuousOn hn
  rcases hs with hs | hs
  · exact Or.inl (fun x hx => sub_pos.mp (hs hx))
  · exact Or.inr (fun x hx => sub_neg.mp (hs hx))

end RegularPathCornerChart
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
