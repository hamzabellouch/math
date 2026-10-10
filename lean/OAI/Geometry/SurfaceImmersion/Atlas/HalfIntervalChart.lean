import OAI.Geometry.SurfaceImmersion.Atlas.MatchedSubsetChart

namespace OAI

/-! Near its left endpoint, a closed nontrivial interval has the same
local topology as the nonnegative real half-line. -/
noncomputable section
open Set Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing

theorem half_interval_chart {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : OpenPartialHomeomorph (Icc (0:ℝ) δ) (Ici (0:ℝ)),
      (⟨0,le_rfl,hδ.le⟩ : Icc (0:ℝ) δ) ∈ c.source ∧
      c ⟨0,le_rfl,hδ.le⟩ = ⟨0,by simp⟩ := by
  let e := (OpenPartialHomeomorph.refl ℝ).restrOpen (Iio δ) isOpen_Iio
  have hsource : (0:ℝ) ∈ e.source := ⟨mem_univ _,hδ⟩
  obtain ⟨c,hc,_,_,hf,_⟩ := matched_subset_chart e (Icc (0:ℝ) δ) (Ici (0:ℝ)) 0 hsource
    ⟨le_rfl,hδ.le⟩ (by
      intro x hx
      change (0 ≤ x ∧ x ≤ δ) ↔ 0 ≤ x
      exact ⟨And.left,fun h => ⟨h,hx.2.le⟩⟩)
  refine ⟨c,hc,?_⟩
  apply Subtype.ext
  exact hf _ hc

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
