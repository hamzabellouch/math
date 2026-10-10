import OAI.Analysis.LipschitzHilbert.Phase.AngularCommonTranslation

namespace OAI

/-! Boundary coincidences are a null set of the common translation. -/

noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.AngularGrid

theorem ae_boundaryDistance_pos (g : AngularGrid) (i : ℕ) (s : ℝ) :
    ∀ᵐ origin : ℝ, 0 < (g.withOrigin origin).boundaryDistance i s := by
  filter_upwards [(Set.countable_range (fun k : ℤ => s-g.width i*k)).ae_notMem volume] with origin ho
  by_contra h
  have hs := (g.withOrigin origin).slope_mem_cell i s
  have hlow : origin+g.width i*((g.withOrigin origin).index i s) ≤ s := hs.1
  have hhigh : s < origin+g.width i*((g.withOrigin origin).index i s)+g.width i := hs.2
  have hd : min (s-(origin+g.width i*((g.withOrigin origin).index i s)))
      (origin+g.width i*((g.withOrigin origin).index i s)+g.width i-s) ≤ 0 := le_of_not_gt h
  rcases min_le_iff.mp hd with hleft | hright
  · apply ho
    refine ⟨(g.withOrigin origin).index i s,?_⟩
    linarith
  · linarith

theorem ae_normalized_boundaryDistance_pos (g : AngularGrid) (i : ℕ) (s : ℝ) :
    ∀ᵐ origin : ℝ, 0 < (g.withOrigin origin).boundaryDistance i s/g.width i :=
  (g.ae_boundaryDistance_pos i s).mono fun _ h => div_pos h (g.width_pos i)

end LipschitzHilbert.AngularGrid

end

end OAI
