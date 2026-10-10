import OAI.Combinatorics.BalancedRyser.Incidence.PrimeStabilityReduction

namespace OAI

namespace Balanced
open scoped _root_.Balanced

universe u

theorem primeStability_of_smallProjective
    (hprojective : ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      Nat.Prime (Fintype.card F) → 100 ≤ Fintype.card F →
      ∀ B : Finset (ProjectivePoint F), B.card ≤ Fintype.card F →
        ((skewProjective B).card : ℝ) <
          (201 / 10000 : ℝ) * (Fintype.card F : ℝ) ^ 2 →
        ∃ l : ProjectiveLine F,
          (Fintype.card F : ℝ) - 2 * (skewProjective B).card /
            ((Fintype.card F : ℝ) + 1) ≤
              ((B.filter (fun P => ProjectiveIncident P l)).card : ℝ)) :
    PrimeStability.{u} := by
  intro F _ _ _ hprime ζ hζ hlarge C hcard hmiss
  have hq : (100 : ℝ) ≤ (Fintype.card F : ℝ) :=
    (le_max_left _ _).trans hlarge
  have hthreshold : 4 / ζ ≤ (Fintype.card F : ℝ) :=
    (le_max_right _ _).trans hlarge
  have hholes : ((skewProjective (dualPointSet C)).card : ℝ) ≤
      ((uncoveredPoints C).card : ℝ) + (Fintype.card F : ℝ) + 1 := by
    exact_mod_cast card_skew_dualPointSet_le C
  have hsmall := StabilityArithmetic.hole_bound hq hmiss hholes
  have hBcard : (dualPointSet C).card ≤ Fintype.card F := by
    simpa only [card_dualPointSet] using hcard
  obtain ⟨l, hl⟩ := hprojective F hprime (by exact_mod_cast hq)
    (dualPointSet C) hBcard hsmall
  have hconclusion :=
    (StabilityArithmetic.reduction_bounds hq hζ hthreshold hmiss hholes).2.2.2
  refine ⟨dualPoint l, ?_⟩
  simpa only [card_dualPointSet_on_line, pencilSize] using hconclusion.le.trans hl

end Balanced

end OAI
