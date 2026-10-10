import OAI.NumberTheory.Ostmann.Construction.SelectedCounterpartBound
import OAI.NumberTheory.Ostmann.Construction.SelectedDiagonalCountBudget

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
open Filter
namespace Ostmann.Construction
open Conclusion DiagonalPermutationCount Arithmetic.HistoryProductWindows

def diagonalFixedFactor (k l : ℕ) : ℝ :=
  ((1+2^l*(6+4*k)).factorial:ℝ)*(((2^l:ℕ):ℝ)^(2*(2^l)))*
    Real.exp (nominalInheritedWidth k l+nominalRemovedWidth k l)

def diagonalFixedOverhead (k : ℕ) : ℝ :=
  1+∑l∈Finset.range (k+1),diagonalFixedFactor k l

theorem diagonalFixedFactor_nonneg (k l : ℕ) : 0≤diagonalFixedFactor k l := by
  unfold diagonalFixedFactor
  positivity

theorem diagonalFixedOverhead_pos (k : ℕ) : 0<diagonalFixedOverhead k := by
  have h := Finset.sum_nonneg (fun l (_ : l∈Finset.range (k+1)) => diagonalFixedFactor_nonneg k l)
  unfold diagonalFixedOverhead
  linarith

theorem diagonalMatchingOverhead_archimedean_le (m k l : ℕ) (hl : l≤k) :
    diagonalMatchingOverhead m k l*
      Real.exp (nominalInheritedWidth k l+nominalRemovedWidth k l)≤diagonalFixedOverhead k := by
  have hn := remaining_nonbulk_card_le m k l
  rw [remainder_nonbulk_card] at hn
  have hf : (((remainingTemplate m k l).length+1-2^l*m).factorial:ℝ)≤
      ((1+2^l*(6+4*k)).factorial:ℝ) := by
    exact_mod_cast Nat.factorial_le hn
  have hlocal : diagonalMatchingOverhead m k l*
      Real.exp (nominalInheritedWidth k l+nominalRemovedWidth k l)≤diagonalFixedFactor k l := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hf (by positivity)) (Real.exp_pos _).le
  have hsum := Finset.single_le_sum
    (fun j (_ : j∈Finset.range (k+1)) => diagonalFixedFactor_nonneg k j)
    (show l∈Finset.range (k+1) from Finset.mem_range.mpr (by omega))
  unfold diagonalFixedOverhead
  linarith

theorem diagonal_fixed_overhead_absorbed_eventually {k : ℕ} (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop,∀l≤k,
      diagonalMatchingOverhead (bulkSize k L) k l*
        Real.exp (nominalInheritedWidth k l+nominalRemovedWidth k l)≤
          Real.exp ((2:ℝ)^l*(bulkSize k L:ℝ)) := by
  filter_upwards [(bulkSize_tendsto_atTop hk).eventually_ge_atTop
    (Real.log (diagonalFixedOverhead k))] with L hL
  intro l hl
  refine (diagonalMatchingOverhead_archimedean_le (bulkSize k L) k l hl).trans ?_
  rw [←Real.exp_log (diagonalFixedOverhead_pos k)]
  apply Real.exp_le_exp.mpr
  refine hL.trans ?_
  have hr : (1:ℝ)≤2^l := one_le_pow₀ (by norm_num)
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hr (Nat.cast_nonneg (bulkSize k L))

end Ostmann.Construction

end

end OAI
