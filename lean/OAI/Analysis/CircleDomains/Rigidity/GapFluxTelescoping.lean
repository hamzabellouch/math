import OAI.Analysis.CircleDomains.Selection.FiniteLineGaps
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

namespace OAI

/-! Finite gap increments equal outer flux minus the increments across
removed intervals, without any continuity assumption on boundary values. -/
open Set
open scoped BigOperators
namespace CircleDomainRigidity

 theorem sum_gap_increments {n : ℕ} (a b : ℝ) (H : Fin n → ℝ × ℝ) (v : ℝ → ℝ) :
    (∑ i, (v (gapsAfterHoles a b H i).2-v (gapsAfterHoles a b H i).1)) =
      v b-v a-∑ i, (v (H i).2-v (H i).1) := by
  rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib]
  have hleft : (∑ i, v (gapsAfterHoles a b H i).1) = v a+∑ i, v (H i).2 := by
    rw [Fin.sum_univ_succ]
    simp only [gapsAfterHoles_zero_fst,gapsAfterHoles_succ_fst]
  have hright : (∑ i, v (gapsAfterHoles a b H i).2) = (∑ i, v (H i).1)+v b := by
    rw [Fin.sum_univ_castSucc]
    simp only [gapsAfterHoles_last_snd,gapsAfterHoles_castSucc_snd]
  rw [hleft,hright]
  ring

end CircleDomainRigidity

end OAI
