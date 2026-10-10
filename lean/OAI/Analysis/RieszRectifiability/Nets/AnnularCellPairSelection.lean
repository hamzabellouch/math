import Mathlib
import OAI.Analysis.RieszRectifiability.Nets.AnnularLatticeScales
import OAI.Analysis.RieszRectifiability.Nets.BoundaryCellGeometry

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

theorem exists_annular_cell_pair {d : ℕ} (μ : Measure (Ambient d))
    (R₀ : ℝ) (hR₀ : 0 < R₀) (k : ℕ) (z : (supportLatticeNets μ R₀ hR₀ k).points)
    (a : Ambient d) (ha : a ∈ μ.support) (hnear : dist a (z : Ambient d) ≤ latticeRadius R₀ k / 8)
    (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R) (hRtop : R ≤ latticeRadius R₀ k / 8)
    (I : ℕ) (hdepth : annularLatticeDepth R₀ k r hr ≤ I) :
    ∃ P : CellHaarPair μ R₀ hR₀ k z I,
      (∀ x ∈ P.innerCell, 2 * dist x a ≤ r) ∧
      (∀ x ∈ P.outerCell, 2 * dist x a ≤ R) ∧
      r ≤ 512 * latticeRadius R₀ (k + P.outerOffset + P.innerOffset) ∧
      R ≤ 512 * latticeRadius R₀ (k + P.outerOffset) := by
  have hR := hr.trans_le hrR
  have hp := latticeRadius_pos R₀ hR₀ k
  let t := annularLatticeDepth R₀ k R hR
  have htpos : 0 < t := annularLatticeDepth_pos R₀ k R hR (by linarith)
  have htu : t ≤ annularLatticeDepth R₀ k r hr :=
    annularLatticeDepth_antitone R₀ k r R hr hR hrR
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le htu
  have htj : t + j ≤ I := by rw [← hj]; exact hdepth
  have huOuter : latticeRadius R₀ (k + t) ≤ R / 8 :=
    annularLatticeDepth_radius_upper R₀ k R hR
  have huInner : latticeRadius R₀ (k + t + j) ≤ r / 8 := by
    rw [Nat.add_assoc, ← hj]
    exact annularLatticeDepth_radius_upper R₀ k r hr
  have hlOuter : R ≤ 512 * latticeRadius R₀ (k + t) :=
    annularLatticeDepth_radius_lower R₀ hR₀ k R hR (by linarith)
  have hlInner : r ≤ 512 * latticeRadius R₀ (k + t + j) := by
    rw [Nat.add_assoc, ← hj]
    exact annularLatticeDepth_radius_lower R₀ hR₀ k r hr (by linarith)
  obtain ⟨w, haw⟩ := supportLatticeCell_cover μ R₀ hR₀ (k + t + j) a ha
  let v := supportLatticeAncestor μ R₀ hR₀ (k + t) j w
  have hav : a ∈ supportLatticeCell μ R₀ hR₀ (k + t) v :=
    supportLatticeCell_nested μ R₀ hR₀ (k + t) j w haw
  have hvz : supportLatticeAncestor μ R₀ hR₀ k t v = z :=
    closed_cell_ancestor_eq_of_interior_point μ R₀ hR₀ k t htpos z v a hav hnear (by linarith)
  let P : CellHaarPair μ R₀ hR₀ k z I :=
    { outerOffset := t, innerOffset := j, depth_bound := htj,
      outerCenter := v, innerCenter := w, outer_ancestor := hvz, inner_ancestor := rfl }
  refine ⟨P, ?_, ?_, hlInner, hlOuter⟩
  · intro x hx
    have hd := clean_cell_dist_to_closed_point μ R₀ hR₀ (k + t + j) w a haw x hx
    linarith
  · intro x hx
    have hd := clean_cell_dist_to_closed_point μ R₀ hR₀ (k + t) v a hav x hx
    linarith

end

end RieszRectifiability

end OAI
