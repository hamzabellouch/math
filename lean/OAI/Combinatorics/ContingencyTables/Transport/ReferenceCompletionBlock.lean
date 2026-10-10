import OAI.Combinatorics.ContingencyTables.Sampling.PhysicalResidualMargins
import OAI.Combinatorics.ContingencyTables.Transport.TableReindex
import Mathlib.Logic.Equiv.Option

namespace OAI

/-! # Fixed reference row and column for the physical completion blocks -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open PhysicalCompletionFibres FirstPaperPhysicalMarginal CompletionCounts

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

abbrev LargeRows (r : I → ℕ) (U : ℕ) := {i // U ≤ r i}
abbrev LargeColumns (c : J → ℕ) (U : ℕ) := {j // U ≤ c j}

noncomputable def referenceRows (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (i₀ : LargeRows r U) (z : PhysicalStates (firstPaperSmall r c U) B r c L)
    (i : Option {i : LargeRows r U // i ≠ i₀}) : ℕ :=
  residualRows (firstPaperSmall r c U) B r c L z ((Equiv.optionSubtypeNe i₀) i).val

noncomputable def referenceColumns (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (j₀ : LargeColumns c U) (z : PhysicalStates (firstPaperSmall r c U) B r c L)
    (j : Option {j : LargeColumns c U // j ≠ j₀}) : ℕ :=
  residualColumns (firstPaperSmall r c U) B r c L z ((Equiv.optionSubtypeNe j₀) j).val

lemma reference_totals (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U)
    (z : PhysicalStates (firstPaperSmall r c U) B r c L)
    (hcap : ∀ i j,firstPaperSmall r c U i j=false →
      (∑ k,residualRows (firstPaperSmall r c U) B r c L z k) ≤ B i j) :
    (∑ i,referenceRows r c U L B i₀ z i)=∑ j,referenceColumns r c U L B j₀ z j := by
  unfold referenceRows referenceColumns
  rw [(Equiv.optionSubtypeNe i₀).sum_comp
    (fun i : LargeRows r U => residualRows (firstPaperSmall r c U) B r c L z i.val),
    (Equiv.optionSubtypeNe j₀).sum_comp
    (fun j : LargeColumns c U => residualColumns (firstPaperSmall r c U) B r c L z j.val)]
  have hr : (∑ i : LargeRows r U,residualRows (firstPaperSmall r c U) B r c L z i.val)=
      ∑ i,residualRows (firstPaperSmall r c U) B r c L z i := by
    convert sum_subtype_eq_of_zero (fun i => U ≤ r i)
      (residualRows (firstPaperSmall r c U) B r c L z)
      (physical_residual_row_zero r c U L B z hcap) using 1
    congr 2
    exact Subsingleton.elim _ _
  have hc : (∑ j : LargeColumns c U,residualColumns (firstPaperSmall r c U) B r c L z j.val)=
      ∑ j,residualColumns (firstPaperSmall r c U) B r c L z j := by
    convert sum_subtype_eq_of_zero (fun j => U ≤ c j)
      (residualColumns (firstPaperSmall r c U) B r c L z)
      (physical_residual_column_zero r c U L B z hcap) using 1
    congr 2
    exact Subsingleton.elim _ _
  rw [hr,hc]
  exact physical_residual_totals _ B r c L z hcap

/-- A single pair of reference indices, fixed independently of the state,
reindexes every actual completion block and retains its exact count. -/
theorem physical_weight_reference_block (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U)
    (z : PhysicalStates (firstPaperSmall r c U) B r c L)
    (hcap : ∀ i j,firstPaperSmall r c U i j=false →
      (∑ k,residualRows (firstPaperSmall r c U) B r c L z k) ≤ B i j) :
    hardMarginal (firstPaperSmall r c U) B r c L (physicalProfile _ B r c L z)=
      (Fintype.card (Table (referenceRows r c U L B i₀ z) (referenceColumns r c U L B j₀ z)):ℝ) := by
  rw [physical_weight_rectangle r c U L B z hcap]
  convert congrArg (fun n : ℕ => (n:ℝ)) (Fintype.card_congr
    (tableReindex (Equiv.optionSubtypeNe i₀) (Equiv.optionSubtypeNe j₀)
      (fun i : LargeRows r U => residualRows (firstPaperSmall r c U) B r c L z i.val)
      (fun j : LargeColumns c U => residualColumns (firstPaperSmall r c U) B r c L z j.val))) using 1
  all_goals congr 3

end ContingencyTables.SmallGraphProfiles

end OAI
