import OAI.Geometry.SurfaceImmersion.Geometry.CompactCurvePieces

namespace OAI

/-! A connected punctured boundary neighborhood meets exactly one
incident edge of the proved finite curve decomposition. -/
noncomputable section
open Set
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X : Type*} [TopologicalSpace X]

theorem unique_boundary_incident_piece (V : Set X) (P : Finset (Set X))
    (hP : ∀ E ∈ P, IsOpen E ∧ Disjoint E V ∧ closure E \ E ⊆ V)
    (hdis : ∀ E ∈ P, ∀ F ∈ P, E ≠ F → Disjoint E F)
    (hcover : Vᶜ = ⋃ E ∈ P, E) {p : X} (hp : p ∈ V)
    {W : Set X} (hW : IsOpen W) (hpW : p ∈ W)
    (hS : IsConnected (W \ {p})) (hSV : W \ {p} ⊆ Vᶜ)
    (hpS : p ∈ closure (W \ {p})) :
    ∃ E ∈ P, p ∈ closure E ∧ ∀ F ∈ P, p ∈ closure F → F = E := by
  classical
  obtain ⟨x,hx⟩ := hS.nonempty
  have hxV := hSV hx
  rw [hcover] at hxV
  obtain ⟨E,hE,hxE⟩ := mem_iUnion₂.mp hxV
  have hSE : W \ {p} ⊆ E :=
    hS.isPreconnected.subset_of_closure_inter_subset (hP E hE).1 ⟨x,hx,hxE⟩ (by
      intro y hy
      by_contra hn
      exact hSV hy.2 ((hP E hE).2.2 ⟨hy.1,hn⟩))
  refine ⟨E,hE,(closure_mono hSE) hpS,?_⟩
  intro F hF hpF
  obtain ⟨y,hyW,hyF⟩ := (mem_closure_iff.mp hpF) W hW hpW
  have hne : y ≠ p := by
    intro he
    exact disjoint_left.mp (hP F hF).2.1 hyF (he ▸ hp)
  have hyE := hSE ⟨hyW,by simpa only [mem_singleton_iff] using hne⟩
  by_contra hFE
  exact disjoint_left.mp (hdis F hF E hE hFE) hyF hyE

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
