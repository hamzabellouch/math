import Mathlib

namespace OAI

/-! Compatibility of the algebraic structures used by the concrete L²
space and by the abstract normed-space estimates. -/
noncomputable section
open MeasureTheory
namespace WeakPureInfiniteness

variable {H : Type*} [NormedAddCommGroup H]

lemma lp_addCommGroup_from_normed :
    (inferInstance : NormedAddCommGroup (Lp H 2 (volume : Measure ℝ))).toAddCommGroup =
      (Lp.instAddCommGroup (E := H) (p := 2) (μ := (volume : Measure ℝ))) := by
  rfl

lemma lp_addCommMonoid_from_normed :
    (inferInstance : NormedAddCommGroup (Lp H 2 (volume : Measure ℝ))).toAddCommGroup.toAddCommMonoid =
      (Lp.instAddCommGroup (E := H) (p := 2) (μ := (volume : Measure ℝ))).toAddCommMonoid := by
  rfl

end WeakPureInfiniteness

end

end OAI
