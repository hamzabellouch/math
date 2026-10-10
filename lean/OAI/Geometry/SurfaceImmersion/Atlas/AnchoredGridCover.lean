import OAI.Geometry.Immersion.ClosedSurface.CompactPartition

namespace OAI

/-! Finite polynomial grids with every selected cell anchored on the compact set. -/
noncomputable section
open Set
namespace ClosedSurfaceR4.PhaseGrid

 theorem compact_anchored_polynomial_grid {K : Set Base} (hK : IsCompact K) :
    ∃ z₀ C : ℝ, 0 < z₀ ∧ z₀ ≤ 1 ∧ 0 < C ∧
      ∀ z : ℝ, 0 < z → z ≤ z₀ → ∃ s : Finset Index,
        (s.card : ℝ) ≤ C/z^12 ∧ K ⊆ coverRegion s (z^6) ∧
        (∀ a ∈ s, ∃ x ∈ K, ‖x-z^6 • center a‖ ≤ 3*z^6) := by
  classical
  obtain ⟨z₀,C,hz₀,hz₀1,hC,hgrid⟩ :=
    compact_subpatch_polynomial_grid hK isOpen_univ (subset_univ _)
  refine ⟨z₀,C,hz₀,hz₀1,hC,?_⟩
  intro z hz hzsmall
  obtain ⟨s,hcard,hcover,_⟩ := hgrid z hz hzsmall
  let t := s.filter (fun a => ∃ x ∈ K, x ∈ cell (z^6) 1 a)
  refine ⟨t,?_,?_,?_⟩
  · exact (show (t.card : ℝ) ≤ (s.card : ℝ) by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)).trans hcard
  · intro x hx
    obtain ⟨a,ha,hxa⟩ := hcover x hx
    exact mem_iUnion.mpr ⟨a,mem_iUnion.mpr ⟨Finset.mem_filter.mpr ⟨ha,x,hx,hxa⟩,hxa⟩⟩
  · intro a ha
    obtain ⟨_,x,hx,hxa⟩ := Finset.mem_filter.mp ha
    refine ⟨x,hx,?_⟩
    have hd := norm_sub_center_lt hxa
    have hp := pow_pos hz 6
    nlinarith

end ClosedSurfaceR4.PhaseGrid

end

end OAI
