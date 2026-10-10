import OAI.Geometry.SurfaceImmersion.Geometry.CompactCurveEndpoint
import OAI.Geometry.SurfaceImmersion.Whitney.OrderedArcEndpointUnique
import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapArcEndpoint

namespace OAI

/-! Compact regular insertions do not change the kernel-axis geometry
of an actual crosscap connection near its singular endpoint. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M] [T2Space M]
variable {f : M → ProjectionTarget 3} {p q : M}

theorem crosscap_source_endpoint_neighborhood (c : SurfaceCrosscapCoordinates f p)
    {Γ : I → M × M} (hΓ : Continuous Γ) (hi : Function.Injective Γ)
    (hzero : Γ 0 = (p,p)) (hone : Γ 1 = (q,q))
    (heq : ∀ u, f (Γ u).1 = f (Γ u).2)
    (hne : ∀ u : I, 0 < (u:ℝ) → (u:ℝ) < 1 → (Γ u).1 ≠ (Γ u).2)
    (hsing : ∀ x, f x = f p → x = p)
    {K : Set M} (hK : IsCompact K) (hpK : p ∉ K) :
    ∃ V : Set M, IsOpen V ∧ p ∈ V ∧
      ∀ x ∈ V, x ∈ Prod.fst '' range Γ ∪ K →
        x ∈ c.source.source ∧ c.source x 0 = 0 := by
  obtain ⟨ε,hε,_,hcoords⟩ := crosscap_arc_endpoint c hΓ hzero heq hne
  obtain ⟨V,hV,hpV,hsmall⟩ := compact_curve_endpoint_neighborhood hΓ.fst
    (ordered_arc_source_start_unique hi hzero hone heq hne hsing) hK hpK hε
  refine ⟨V,hV,hpV,?_⟩
  intro x hx hxi
  have hxrange : x ∈ range (fun t => (Γ t).1) ∪ K := by
    rcases hxi with ⟨z,⟨u,hu⟩,hz⟩ | hk
    · exact Or.inl ⟨u,(congrArg Prod.fst hu).trans hz⟩
    · exact Or.inr hk
  obtain ⟨u,hu,rfl⟩ := hsmall x hx hxrange
  exact ⟨(hcoords u hu.le).1,(hcoords u hu.le).2.2.1⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
