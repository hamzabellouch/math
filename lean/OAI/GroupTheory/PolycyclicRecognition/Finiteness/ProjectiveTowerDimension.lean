import OAI.GroupTheory.PolycyclicRecognition.Finiteness.IntegralProjectiveTower

namespace OAI

/-! # A projective tail bounds the dimension at the base of a tower -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
variable {G : Type} [Group G]

theorem IntegralProjectiveTower.dimension_of_tail (T : IntegralProjectiveTower G)
    (n d : ℕ) (h : HasProjectiveDimensionLE (T.obj n) d) :
    HasProjectiveDimensionLE (T.obj 0) (n + d) := by
  induction n generalizing d with
  | zero => simpa only [Nat.zero_add] using h
  | succ n ih =>
    have hprev : HasProjectiveDimensionLE (T.obj n) (d + 1) :=
      (T.shortExact n).hasProjectiveDimensionLT_X₃ (d + 1) h
        (hasProjectiveDimensionLT_of_ge (T.projectiveObj n) 1 (d + 2) (by omega))
    simpa only [Nat.succ_add, Nat.add_succ] using ih (d + 1) hprev

theorem IntegralProjectiveTower.dimension_of_projective_tail (T : IntegralProjectiveTower G)
    (n : ℕ) [Projective (T.obj n)] : HasProjectiveDimensionLE (T.obj 0) n := by
  simpa only [Nat.add_zero] using T.dimension_of_tail n 0 inferInstance

end PolycyclicRecognition

end

end OAI
