import OAI.Geometry.SurfaceImmersion.Geometry.LinePuncturedNeighborhood
import OAI.Geometry.SurfaceImmersion.Geometry.CurveEdgeParametrization

namespace OAI

/-! Ordinary vertices of the interval decomposition have exactly two incident edges. -/
noncomputable section
open Set Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X : Type*} [TopologicalSpace X] [T2Space X]

omit [T2Space X] in
private theorem connected_subset_piece (V : Set X) (P : Finset (Set X))
    (hP : ∀ E ∈ P, IsOpen E ∧ Disjoint E V ∧ closure E \ E ⊆ V)
    (hcover : Vᶜ = ⋃ E ∈ P, E) {S : Set X} (hS : IsConnected S)
    (hSV : S ⊆ Vᶜ) : ∃ E ∈ P, S ⊆ E := by
  obtain ⟨x,hx⟩ := hS.nonempty
  have hxV := hSV hx
  rw [hcover] at hxV
  obtain ⟨E,hE,hxE⟩ := mem_iUnion₂.mp hxV
  refine ⟨E,hE,hS.isPreconnected.subset_of_closure_inter_subset (hP E hE).1
    ⟨x,hx,hxE⟩ ?_⟩
  intro y hy
  by_contra hn
  exact hSV hy.2 ((hP E hE).2.2 ⟨hy.1,hn⟩)

theorem ordinary_vertex_degree_two (V : Set X) (hV : V.Finite) (P : Finset (Set X))
    (hP : ∀ E ∈ P, IsOpen E ∧ Disjoint E V ∧ closure E \ E ⊆ V)
    (hdis : ∀ E ∈ P, ∀ F ∈ P, E ≠ F → Disjoint E F)
    (hcover : Vᶜ = ⋃ E ∈ P, E)
    (hwitness : ∀ E ∈ P, Nonempty (CurveEdgeWitness V E))
    {p : X} (hp : p ∈ V) (c : OpenPartialHomeomorph X ℝ) (hc : p ∈ c.source) :
    ∃ E ∈ P, ∃ F ∈ P, E ≠ F ∧ p ∈ closure E ∧ p ∈ closure F ∧
      ∀ G ∈ P, p ∈ closure G → G = E ∨ G = F := by
  classical
  obtain ⟨W,S,T,hW,hpW,hS,hT,_,hsplit,hSV,hpS,hpT⟩ :=
    line_punctured_neighborhood c hc V hV
  obtain ⟨E,hE,hSE⟩ := connected_subset_piece V P hP hcover hS
    (fun _ hx => hSV (Or.inl hx))
  obtain ⟨F,hF,hTF⟩ := connected_subset_piece V P hP hcover hT
    (fun _ hx => hSV (Or.inr hx))
  have hpE : p ∈ closure E := closure_mono hSE hpS
  have hpF : p ∈ closure F := closure_mono hTF hpT
  have hEF : E ≠ F := by
    intro heq
    have hWE : W ⊆ closure E := by
      intro x hx
      by_cases hxp : x = p
      · simpa only [hxp] using hpE
      · have hxs : x ∈ W \ {p} := ⟨hx,by simpa only [mem_singleton_iff] using hxp⟩
        rw [hsplit] at hxs
        rcases hxs with hs | ht
        · exact subset_closure (hSE hs)
        · exact subset_closure (heq.symm ▸ hTF ht)
    have hpInt : p ∈ interior (closure E) := interior_maximal hWE hW hpW
    have hpnot : p ∉ E := fun h => disjoint_left.mp (hP E hE).2.1 h hp
    exact (Classical.choice (hwitness E hE)).frontier_not_interior_closure c hc
      ⟨hpE,hpnot⟩ hpInt
  refine ⟨E,hE,F,hF,hEF,hpE,hpF,?_⟩
  intro G hG hpG
  obtain ⟨x,hxW,hxG⟩ := (mem_closure_iff.mp hpG) W hW hpW
  have hxp : x ≠ p := by
    intro heq
    exact disjoint_left.mp (hP G hG).2.1 hxG (heq ▸ hp)
  have hxST : x ∈ S ∪ T := hsplit ▸ ⟨hxW,by simpa only [mem_singleton_iff] using hxp⟩
  rcases hxST with hxS | hxT
  · left
    by_contra hGE
    exact disjoint_left.mp (hdis G hG E hE hGE) hxG (hSE hxS)
  · right
    by_contra hGF
    exact disjoint_left.mp (hdis G hG F hF hGF) hxG (hTF hxT)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
