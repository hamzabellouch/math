import OAI.Geometry.SurfaceImmersion.Geometry.CurveEdgePaths
import OAI.Geometry.SurfaceImmersion.Geometry.CurveIncidenceGraph

namespace OAI

/-! Localization of a full edge path at its two graph vertices and its
single open interval edge. -/
noncomputable section
open Set
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X : Type*} [TopologicalSpace X] [T2Space X]

theorem curve_edge_frontier_endpoints {V : Set X} {E : Set X}
    (w : CurveEdgeWitness V E) (hdis : Disjoint E V) (a b : V) (hne : a ≠ b)
    (ha : a.val ∈ closure E) (hb : b.val ∈ closure E) :
    closure E \ E = {a.val,b.val} := by
  have hne' : a.val ≠ b.val := fun h => hne (Subtype.ext h)
  rcases (w.endpoint_iff hdis a.property).mp ha with hal | har <;>
    rcases (w.endpoint_iff hdis b.property).mp hb with hbl | hbr
  · exact False.elim (hne' (hal.trans hbl.symm))
  · rw [w.frontier_eq,hal,hbr]
  · rw [w.frontier_eq,har,hbl,pair_comm]
  · exact False.elim (hne' (har.trans hbr.symm))

theorem curve_edge_path_localization {V : Set X} {P : Finset (Set X)}
    (hP : ∀ E ∈ P, Disjoint E V)
    (hdis : ∀ E ∈ P, ∀ F ∈ P, E ≠ F → Disjoint E F)
    (E : P) (w : CurveEdgeWitness V E.val) (a b : V) (hne : a ≠ b)
    (ha : a.val ∈ closure E.val) (hb : b.val ∈ closure E.val)
    (γ : Path a.val b.val) (hrange : range γ = closure E.val) :
    (∀ v : V, v.val ∈ range γ → v = a ∨ v = b) ∧
    (∀ F : P, (range γ ∩ F.val).Nonempty → F = E) := by
  have hfront := curve_edge_frontier_endpoints w (hP E.val E.property) a b hne ha hb
  constructor
  · intro v hv
    have hn : v.val ∉ E.val := fun h => disjoint_left.mp (hP E.val E.property) h v.property
    have hv' : v.val ∈ closure E.val \ E.val := ⟨hrange ▸ hv,hn⟩
    rw [hfront] at hv'
    rcases hv' with he | he
    · exact Or.inl (Subtype.ext he)
    · exact Or.inr (Subtype.ext (mem_singleton_iff.mp he))
  · rintro F ⟨x,hxγ,hxF⟩
    by_contra hFE
    have hxcl : x ∈ closure E.val := hrange ▸ hxγ
    by_cases hxE : x ∈ E.val
    · exact disjoint_left.mp (hdis F.val F.property E.val E.property
        (fun h => hFE (Subtype.ext h))) hxF hxE
    · have hxV : x ∈ V := by
        have hx : x ∈ closure E.val \ E.val := ⟨hxcl,hxE⟩
        rw [w.frontier_eq] at hx
        rcases hx with he | he
        · exact he ▸ w.left_mem
        · exact (mem_singleton_iff.mp he) ▸ w.right_mem
      exact disjoint_left.mp (hP F.val F.property) hxF hxV

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
