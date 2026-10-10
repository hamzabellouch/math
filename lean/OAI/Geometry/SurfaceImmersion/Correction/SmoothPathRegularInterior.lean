import OAI.Geometry.SurfaceImmersion.Whitney.SmoothFiniteRegularPath

namespace OAI

/-! Interior regularity survives the finite smoothing: injectivity excludes
both fixed endpoints from every interior parameter. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {p q : M} {γ : Path p q}

theorem smoothed_arc_interior {O : Set M}
    (hγO : ∀ t : unitInterval, 0 < (t:ℝ) → (t:ℝ) < 1 → γ t ∈ O)
    (P : SmoothCompactArc planeModel M) {K : Set M} (hKO : K ⊆ O)
    (hPs : P.curve P.start = p) (hPf : P.curve P.finish = q)
    (hPi : P.curve '' Icc P.start P.finish ⊆ range γ ∪ K) :
    ∀ t ∈ Ioo P.start P.finish, P.curve t ∈ O := by
  intro t ht
  rcases hPi ⟨t,⟨ht.1.le,ht.2.le⟩,rfl⟩ with h | h
  · obtain ⟨u,hu⟩ := h
    have hu0 : u ≠ 0 := by
      intro he
      have heq : P.curve t = P.curve P.start := by rw [← hu,he,Path.source,hPs]
      exact (ne_of_gt ht.1) (P.injective ⟨ht.1.le,ht.2.le⟩
        (left_mem_Icc.mpr P.start_lt_finish.le) heq)
    have hu1 : u ≠ 1 := by
      intro he
      have heq : P.curve t = P.curve P.finish := by rw [← hu,he,Path.target,hPf]
      exact (ne_of_lt ht.2) (P.injective ⟨ht.1.le,ht.2.le⟩
        (right_mem_Icc.mpr P.start_lt_finish.le) heq)
    rw [← hu]
    exact hγO u (lt_of_le_of_ne u.property.1 (fun he => hu0 (Subtype.ext he.symm)))
      (lt_of_le_of_ne u.property.2 (fun he => hu1 (Subtype.ext he)))
  · exact hKO h

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
