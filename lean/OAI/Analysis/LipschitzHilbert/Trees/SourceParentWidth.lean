import OAI.Analysis.LipschitzHilbert.Trees.SourceCountParameters

namespace OAI

/-! The parent residual cone fits the manuscript's physical packet
width W=mw. The actual dyadic branching is much smaller than m;
no enlargement of the source packet profiles is required. -/

noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert.SourceParameters

theorem eventually_parent_reference_width (cone : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ m w W : ℝ,
      Real.exp (L^(9/10:ℝ)) ≤ m → 0 < w → W = m*w →
      (cone+branching L^3)*w ≤ W ∧ (cone+branching L^2)*w ≤ W := by
  filter_upwards [eventually_branching_ge (max 2 cone),eventually_branching_separation]
    with L hlarge hseparation
  intro m w W hm hw hW
  have hB2 : 2 ≤ branching L := (le_max_left _ _).trans hlarge
  have hB1 : 1 ≤ branching L := by linarith
  have hcone : cone ≤ branching L := (le_max_right _ _).trans hlarge
  have hB3 : branching L ≤ branching L^3 := le_self_pow₀ hB1 (by norm_num)
  have hc : cone+branching L^3 ≤ branching L^4 := by
    have hp : 0 ≤ branching L^3 := by positivity
    have hh := mul_le_mul_of_nonneg_right hB2 hp
    rw [show branching L*branching L^3 = branching L^4 by ring] at hh
    linarith
  have hbudget : cone+branching L^3 ≤ m := hc.trans
    ((pow_le_pow_right₀ hB1 (by norm_num : 4 ≤ 100)).trans (hseparation.trans hm))
  have hsmall : cone+branching L^2 ≤ m := by
    have hp := pow_le_pow_right₀ hB1 (by norm_num : 2 ≤ 3)
    linarith
  subst W
  exact ⟨mul_le_mul_of_nonneg_right hbudget hw.le,mul_le_mul_of_nonneg_right hsmall hw.le⟩

end LipschitzHilbert.SourceParameters

end

end OAI
