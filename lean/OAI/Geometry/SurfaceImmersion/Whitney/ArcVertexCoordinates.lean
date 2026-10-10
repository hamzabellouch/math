import OAI.Geometry.SurfaceImmersion.Geometry.SubarcTopology
import OAI.Geometry.SurfaceImmersion.Geometry.FiniteIntervalChopping

namespace OAI

/-! A finite ambient vertex set induces a finite ordered cut set in
each embedded arc. -/
noncomputable section
open Set
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X : Type*} [TopologicalSpace X]

theorem arc_vertex_coordinates (A : CompactCurveArc X) (V : Set X) (hV : V.Finite) :
    ∃ S : Finset ℝ,
      (∀ t : Icc A.left A.right, (t:ℝ) ∈ S ↔ A.map t ∈ V) ∧
      ∀ r ∈ S, A.left ≤ r ∧ r ≤ A.right := by
  classical
  have hpre : (A.map ⁻¹' V).Finite := hV.preimage A.embedding.injective.injOn
  let R : Set ℝ := Subtype.val '' (A.map ⁻¹' V)
  have hR : R.Finite := hpre.image Subtype.val
  refine ⟨hR.toFinset,?_,?_⟩
  · intro t
    rw [Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨u,hu,he⟩
      change A.map u ∈ V at hu
      have hut : u = t := Subtype.ext he
      simpa only [hut] using hu
    · intro ht
      exact ⟨t,ht,rfl⟩
  · intro r hr
    rw [Set.Finite.mem_toFinset] at hr
    obtain ⟨t,_,rfl⟩ := hr
    exact t.property

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
