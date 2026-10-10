import Mathlib.Tactic
import OAI.Combinatorics.BalancedRyser.Incidence.AffineMomentAlgebraLemmas
import OAI.Combinatorics.BalancedRyser.Incidence.Projective2
import OAI.Combinatorics.BalancedRyser.Incidence.ProjectiveStability
import OAI.Combinatorics.BalancedRyser.Incidence.Stability

namespace OAI

namespace Balanced
open scoped _root_.Balanced

universe u

theorem primeStability_of_szonyiWeiner
    (hprojective : SzonyiWeinerStability.{u}) : PrimeStability.{u} := by
  intro F _ _ _ hprime ζ hζ hlarge C hcard hmiss
  have hq : (100 : ℝ) ≤ (Fintype.card F : ℝ) :=
    (le_max_left _ _).trans hlarge
  have hthreshold : 4 / ζ ≤ (Fintype.card F : ℝ) :=
    (le_max_right _ _).trans hlarge
  have hholes : ((skewProjective (dualPointSet C)).card : ℝ) ≤
      ((uncoveredPoints C).card : ℝ) + (Fintype.card F : ℝ) + 1 := by
    exact_mod_cast card_skew_dualPointSet_le C
  obtain ⟨hβpos, hsize, hskew, hconclusion⟩ :=
    StabilityArithmetic.reduction_bounds hq hζ hthreshold hmiss hholes
  have hBsize : ((dualPointSet C).card : ℝ) ≤
      (3 / 2 : ℝ) * ((Fintype.card F : ℝ) + 1) -
        (⌊(Fintype.card F : ℝ) / 3⌋ : ℝ) := by
    rw [card_dualPointSet]
    exact (Nat.cast_le.mpr hcard).trans hsize
  obtain ⟨l, hl⟩ := hprojective F hprime (dualPointSet C)
    (⌊(Fintype.card F : ℝ) / 3⌋ : ℝ) hβpos hBsize hskew
  refine ⟨dualPoint l, ?_⟩
  have hbound := hconclusion.le.trans hl
  simpa only [card_dualPointSet_on_line, pencilSize] using hbound

end Balanced

end OAI
