import Mathlib

namespace OAI

universe uX

noncomputable section

namespace Problem326.Geometry

/-- Boundary exclusion traps any preconnected set that meets the interior.
This is the purely topological step in the plateau-polytope construction. -/
theorem subset_interior_of_disjoint_frontier
    {X : Type uX} [TopologicalSpace X] {K B : Set X}
    (hK : IsPreconnected K) (hmeet : (K ∩ interior B).Nonempty)
    (hboundary : Disjoint K (frontier B)) : K ⊆ interior B := by
  apply hK.subset_of_closure_inter_subset isOpen_interior hmeet
  intro x hx
  by_contra hnot
  apply Set.disjoint_left.mp hboundary hx.2
  exact ⟨closure_mono interior_subset hx.1, hnot⟩

/-- A closed preconnected plateau that meets the interior of a compact box
and misses its boundary is compact. No boundedness assumption on the
ambient compatibility class is needed. -/
theorem isCompact_of_disjoint_frontier
    {X : Type uX} [TopologicalSpace X] {K B : Set X}
    (hKclosed : IsClosed K) (hKconn : IsPreconnected K)
    (hBcompact : IsCompact B) (hmeet : (K ∩ interior B).Nonempty)
    (hboundary : Disjoint K (frontier B)) : IsCompact K := by
  apply hBcompact.of_isClosed_subset hKclosed
  exact (subset_interior_of_disjoint_frontier hKconn hmeet hboundary).trans interior_subset

end Problem326.Geometry

namespace Problem326.Geometry

/-- A continuous curve cannot leave an interior if each segment in the
closed ambient set is forbidden from ending on its boundary. -/
theorem mapsTo_interior_of_no_first_boundary
    {X : Type uX} [TopologicalSpace X] {B : Set X} {T : ℝ}
    {x : ℝ → X} (hT : 0 ≤ T) (hB : IsClosed B)
    (hx : ContinuousOn x (Set.Icc 0 T)) (hx0 : x 0 ∈ interior B)
    (hblock : ∀ τ ∈ Set.Icc 0 T,
      Set.MapsTo x (Set.Icc 0 τ) B → x τ ∉ frontier B) :
    Set.MapsTo x (Set.Icc 0 T) (interior B) := by
  have hconn : IsPreconnected (x '' Set.Icc 0 T) :=
    isPreconnected_Icc.image x hx
  have hmeet : ((x '' Set.Icc 0 T) ∩ interior B).Nonempty :=
    ⟨x 0, ⟨0, ⟨le_rfl, hT⟩, rfl⟩, hx0⟩
  suffices hd : Disjoint (x '' Set.Icc 0 T) (frontier B) by
    intro t ht
    exact subset_interior_of_disjoint_frontier hconn hmeet hd ⟨t, ht, rfl⟩
  by_contra hnot
  have hnonempty : (Set.Icc 0 T ∩ x ⁻¹' frontier B).Nonempty := by
    obtain ⟨z, hz, hb⟩ := Set.not_disjoint_iff.mp hnot
    obtain ⟨t, ht, rfl⟩ := hz
    exact ⟨t, ht, hb⟩
  have hc : IsCompact (Set.Icc 0 T ∩ x ⁻¹' frontier B) := by
    exact isCompact_Icc.of_isClosed_subset
      (hx.preimage_isClosed_of_isClosed isClosed_Icc isClosed_frontier)
      Set.inter_subset_left
  obtain ⟨τ, hτ, hmin⟩ := hc.exists_isMinOn hnonempty continuousOn_id
  apply hblock τ hτ.1 ?_ hτ.2
  intro s hs
  rcases hs.2.eq_or_lt with hst | hst
  · simpa [hst] using hB.frontier_subset hτ.2
  · have hsub : Set.Icc 0 s ⊆ Set.Icc 0 T :=
      Set.Icc_subset_Icc le_rfl (le_trans hs.2 hτ.1.2)
    have hd : Disjoint (x '' Set.Icc 0 s) (frontier B) := by
      apply Set.disjoint_left.mpr
      rintro z ⟨t, ht, rfl⟩ hb
      have hτt : τ ≤ t := hmin ⟨hsub ht, hb⟩
      exact (not_le_of_gt hst) (le_trans hτt ht.2)
    have hm : ((x '' Set.Icc 0 s) ∩ interior B).Nonempty :=
      ⟨x 0, ⟨0, ⟨le_rfl, hs.1⟩, rfl⟩, hx0⟩
    exact interior_subset
      (subset_interior_of_disjoint_frontier
        (isPreconnected_Icc.image x (hx.mono hsub)) hm hd
        ⟨s, ⟨hs.1, le_rfl⟩, rfl⟩)

end Problem326.Geometry

namespace Problem326.Geometry

/-- Monotonicity inside a box, together with a global ceiling and exclusion
of boundary maximizers, confines a whole continuous segment to its plateau. -/
theorem mapsTo_plateau_of_monotone_on_box
    {X : Type uX} [TopologicalSpace X] {B : Set X} {T M : ℝ}
    {x : ℝ → X} {F : X → ℝ} (hT : 0 ≤ T) (hB : IsClosed B)
    (hx : ContinuousOn x (Set.Icc 0 T)) (hx0 : x 0 ∈ interior B)
    (hFM : ∀ z, F z ≤ M) (hF0 : F (x 0) = M)
    (hboundary : ∀ z ∈ frontier B, F z ≠ M)
    (hmono : ∀ τ ∈ Set.Icc 0 T, Set.MapsTo x (Set.Icc 0 τ) B →
      MonotoneOn (F ∘ x) (Set.Icc 0 τ)) :
    Set.MapsTo x (Set.Icc 0 T) {z | z ∈ interior B ∧ F z = M} := by
  have hinside : Set.MapsTo x (Set.Icc 0 T) (interior B) := by
    apply mapsTo_interior_of_no_first_boundary hT hB hx hx0
    intro τ hτ hseg hb
    apply hboundary (x τ) hb
    apply le_antisymm (hFM _)
    calc
      M = F (x 0) := hF0.symm
      _ ≤ F (x τ) := hmono τ hτ hseg ⟨le_rfl, hτ.1⟩ ⟨hτ.1, le_rfl⟩ hτ.1
  have hseg : Set.MapsTo x (Set.Icc 0 T) B :=
    fun t ht => interior_subset (hinside ht)
  intro t ht
  refine ⟨hinside ht, le_antisymm (hFM _) ?_⟩
  calc
    M = F (x 0) := hF0.symm
    _ ≤ F (x t) := hmono T ⟨hT, le_rfl⟩ hseg ⟨le_rfl, hT⟩ ht ht.1

end Problem326.Geometry

end

end OAI
