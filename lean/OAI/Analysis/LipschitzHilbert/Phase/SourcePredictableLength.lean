import OAI.Analysis.LipschitzHilbert.Estimates.StoppingScaleIntervals

namespace OAI

/-! Packets surviving a child level have the original horizontal length
needed by the unconditional derivative estimate on its averaging cell. -/

noncomputable section
namespace LipschitzHilbert.AngularGrid

theorem source_eligible_length_lower (g : AngularGrid) {w B length : ℝ}
    (_hw : 0 < w) (hB : 0 < B) (hlength : 0 < length) (level : ℕ)
    (he : g.eligible (g.rootWidth/B^2) (w/length) level) :
    B^2*w/g.width level ≤ length := by
  have hprec := (g.eligible_iff_precision_le (g.rootWidth/B^2) (w/length) level).mp he
  have heq : (g.rootWidth/B^2)/(g.branching:ℝ)^level = g.width level/B^2 := by
    simp only [width]
    ring
  rw [heq] at hprec
  have hm := mul_le_mul_of_nonneg_left ((div_le_iff₀ hlength).mp hprec) (sq_nonneg B)
  have hcancel : B^2*((g.width level/B^2)*length) = g.width level*length := by
    field_simp [(sq_pos_of_pos hB).ne']
  rw [hcancel] at hm
  exact (div_le_iff₀ (g.width_pos level)).mpr (by simpa only [mul_comm] using hm)

end LipschitzHilbert.AngularGrid

namespace LipschitzHilbert.SourceLabeledLattice

variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

/-- The stopping level is the actual last eligible level of the original
packet length; surviving it implies the predictable-length lower bound. -/
theorem source_stopping_length_lower (P : SourceLabeledLattice N κ Label Item)
    (g : AngularGrid) {w B : ℝ} (hw : 0 < w) (hB : 0 < B)
    (hzero : ∀ j, g.eligible (g.rootWidth/B^2) (w/P.length j) 0)
    (level : ℕ) (j : Fin N)
    (hstop : level ≤ g.lastEligible (g.rootWidth/B^2) (w/P.length j)
      (div_pos hw (P.length_pos j))) :
    B^2*w/g.width level ≤ P.length j := by
  apply g.source_eligible_length_lower hw hB (P.length_pos j) level
  exact (g.eligible_iff_le_lastEligible _ _ (div_pos hw (P.length_pos j)) (hzero j) level).mpr hstop

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
