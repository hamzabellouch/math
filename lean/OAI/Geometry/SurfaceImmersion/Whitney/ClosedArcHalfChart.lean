import OAI.Geometry.SurfaceImmersion.Atlas.EmbeddingNeighborhoodChart
import OAI.Geometry.SurfaceImmersion.Atlas.HalfIntervalChart

namespace OAI

/-! An embedded half-arc containing a relative neighborhood provides
an actual half-line chart of the ambient subspace. -/
noncomputable section
open Set Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X : Type*} [TopologicalSpace X]

theorem closed_arc_half_chart {K : Set X} {δ : ℝ} (hδ : 0 < δ)
    (γ : Icc (0:ℝ) δ → X) (hγ : IsEmbedding γ)
    (hmem : ∀ t, γ t ∈ K) {V : Set X} (hV : IsOpen V)
    (hpV : γ ⟨0,le_rfl,hδ.le⟩ ∈ V) (hsub : K ∩ V ⊆ range γ) :
    ∃ c : OpenPartialHomeomorph K (Ici (0:ℝ)),
      (⟨γ ⟨0,le_rfl,hδ.le⟩,hmem _⟩ : K) ∈ c.source ∧
      c ⟨γ ⟨0,le_rfl,hδ.le⟩,hmem _⟩ = ⟨0,by simp⟩ := by
  let g : Icc (0:ℝ) δ → K := K.codRestrict γ hmem
  have hg : IsEmbedding g := hγ.codRestrict K hmem
  let W : Set K := (↑) ⁻¹' V
  have hW : IsOpen W := hV.preimage continuous_subtype_val
  have hWsub : W ⊆ range g := by
    intro z hz
    obtain ⟨t,ht⟩ := hsub ⟨z.property,hz⟩
    exact ⟨t,Subtype.ext ht⟩
  obtain ⟨a,ha,ha0⟩ := embedding_neighborhood_chart g hg ⟨0,le_rfl,hδ.le⟩ hW hpV hWsub
  obtain ⟨b,hb,hb0⟩ := half_interval_chart hδ
  refine ⟨a.trans b,?_,?_⟩
  · change g ⟨0,le_rfl,hδ.le⟩ ∈ a.source ∧ a (g ⟨0,le_rfl,hδ.le⟩) ∈ b.source
    exact ⟨ha,by rw [ha0]; exact hb⟩
  · change b (a (g ⟨0,le_rfl,hδ.le⟩)) = _
    rw [ha0,hb0]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
