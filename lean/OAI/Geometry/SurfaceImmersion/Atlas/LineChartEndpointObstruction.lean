import OAI.Geometry.SurfaceImmersion.Geometry.IntervalNoInteriorExtremum
import OAI.Geometry.SurfaceImmersion.Atlas.EmbeddingNeighborhoodChart

namespace OAI

/-! An endpoint of an embedded compact interval cannot contain a
neighborhood of a point with a real-line chart. -/
noncomputable section
open Set Filter Metric Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X : Type*} [TopologicalSpace X]

theorem line_chart_not_interval_endpoint
    (d : OpenPartialHomeomorph X ℝ) {a b : ℝ}
    (c : OpenPartialHomeomorph X (Icc a b)) {p : X}
    (hd : p ∈ d.source) (hc : p ∈ c.source)
    (hend : (c p:ℝ) = a ∨ (c p:ℝ) = b) : False := by
  let t₀ := d p
  let U := d.target ∩ d.symm ⁻¹' c.source
  have hU : IsOpen U := d.isOpen_inter_preimage_symm c.open_source
  have hpU : t₀ ∈ U := by
    exact ⟨d.map_source hd,by change d.symm (d p) ∈ c.source; rwa [d.left_inv hd]⟩
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hpU)
  let J := Ioo (t₀-r) (t₀+r)
  have hJU : J ⊆ U := by
    intro t ht
    apply hsub
    rw [mem_ball,Real.dist_eq,abs_lt]
    constructor <;> dsimp [J] at ht <;> linarith [ht.1,ht.2]
  let f : ℝ → ℝ := fun t => (c (d.symm t):ℝ)
  have hf : ContinuousOn f J :=
    continuous_subtype_val.continuousOn.comp
      (c.continuousOn.comp (d.continuousOn_symm.mono (fun t ht => (hJU ht).1))
        (fun t ht => (hJU ht).2)) (fun _ _ => mem_univ _)
  have hi : InjOn f J := by
    intro t ht u hu he
    apply d.symm.injOn (hJU ht).1 (hJU hu).1
    apply c.injOn (hJU ht).2 (hJU hu).2
    exact Subtype.ext he
  have ht₀ : t₀ ∈ J := by
    change t₀-r < t₀ ∧ t₀ < t₀+r
    constructor <;> linarith
  have hfp : f t₀ = (c p:ℝ) := by dsimp [f,t₀]; rw [d.left_inv hd]
  rcases hend with hend | hend
  · apply injective_interval_no_minimum ht₀ hf hi
    intro t _
    rw [hfp,hend]
    exact (c (d.symm t)).property.1
  · apply injective_interval_no_maximum ht₀ hf hi
    intro t _
    rw [hfp,hend]
    exact (c (d.symm t)).property.2

theorem compact_arc_endpoint_not_interior
    (d : OpenPartialHomeomorph X ℝ) {a b : ℝ} (hab : a ≤ b)
    (γ : Icc a b → X) (hγ : IsEmbedding γ) {p : X} (hp : p ∈ d.source)
    (hend : p = γ ⟨a,le_rfl,hab⟩ ∨ p = γ ⟨b,hab,le_rfl⟩) :
    p ∉ interior (range γ) := by
  intro hpin
  rcases hend with hend | hend
  · obtain ⟨c,hc,hcp⟩ := embedding_neighborhood_chart γ hγ ⟨a,le_rfl,hab⟩
      isOpen_interior (hend ▸ hpin) interior_subset
    apply line_chart_not_interval_endpoint d c hp (hend.symm ▸ hc)
    left
    rw [hend,hcp]
  · obtain ⟨c,hc,hcp⟩ := embedding_neighborhood_chart γ hγ ⟨b,hab,le_rfl⟩
      isOpen_interior (hend ▸ hpin) interior_subset
    apply line_chart_not_interval_endpoint d c hp (hend.symm ▸ hc)
    right
    rw [hend,hcp]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
