import OAI.Combinatorics.ContingencyTables.Sampling.PhysicalEdgeMargins
import OAI.Combinatorics.ContingencyTables.Transport.ReferenceCompletionBounds
import OAI.Combinatorics.ContingencyTables.Sampling.SmallCompletionAcceptance
import OAI.Combinatorics.ContingencyTables.Transport.TranslatedCompletionCounts

namespace OAI

/-! # Half of every physical completion block accepts an adjacent translation -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open PhysicalCompletionFibres FirstPaperPhysicalMarginal CompletionCounts PaddedCompletions
open CompletionTranslation

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

omit [LinearOrder I] [LinearOrder J] in
lemma reference_dimension_ge_fourteen (r : I → ℕ) (c : J → ℕ) (U : ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U) :
    14 ≤ dimensionAllowance (I := I) (J := J) := by
  have hi : 0 < Fintype.card I := Fintype.card_pos_iff.mpr ⟨i₀.val⟩
  have hj : 0 < Fintype.card J := Fintype.card_pos_iff.mpr ⟨j₀.val⟩
  unfold dimensionAllowance
  nlinarith

theorem reference_edge_acceptance (r : I → ℕ) (c : J → ℕ) (U : ℕ)
    (B : I → J → ℕ)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U)
    (hcap : ∀ z : PhysicalStates (firstPaperSmall r c U) B r c
      ((dimensionAllowance (I := I) (J := J))^12),∀ i j,
      firstPaperSmall r c U i j=false →
      (∑ k,residualRows (firstPaperSmall r c U) B r c _ z k) ≤ B i j)
    (x y : PhysicalStates (firstPaperSmall r c U) B r c
      ((dimensionAllowance (I := I) (J := J))^12))
    (hxy : physicalAdjacent r c U _ B hB x y) :
    (blockCount (referenceRows r c U _ B i₀) (referenceColumns r c U _ B j₀) x:ℝ)/2 ≤
      acceptedCount (referenceRows r c U _ B i₀) (referenceColumns r c U _ B j₀) x y := by
  let d := dimensionAllowance (I := I) (J := J)
  let R := referenceRows r c U (d^12) B i₀
  let P := referenceColumns r c U (d^12) B j₀
  have hm := physical_edge_residual_margins r c U (d^12) B hB hcap x y hxy
  have hr (i) : |(R y i:ℤ)-R x i| ≤ 2 := hm.1 ((Equiv.optionSubtypeNe i₀) i).val
  have hp (j) : |(P y j:ℤ)-P x j| ≤ 2 := hm.2 ((Equiv.optionSubtypeNe j₀) j).val
  have hd := reference_block_dimensions r c U i₀ j₀
  have hD (i j) : |between (R x) (R y) (P x) (P y) i j| ≤ (10*d:ℕ) := by
    have hs := star_abs_le (fun i => (R y i:ℤ)-R x i)
      (fun j => (P y j:ℤ)-P x j) 2 (by norm_num) hr hp i j
    have hc : (Fintype.card {j : LargeColumns c U // j≠j₀}:ℤ)+1 ≤ d := by
      exact_mod_cast (show Fintype.card {j : LargeColumns c U // j≠j₀}+1 ≤ d by
        simpa only [Fintype.card_option] using hd.2.1)
    change |star _ _ i j| ≤ _
    push_cast
    nlinarith
  exact reference_acceptance_half (R x) (P x) (between (R x) (R y) (P x) (P y))
    (reference_totals r c U (d^12) B i₀ j₀ x (hcap x)) (fun _ _ => rfl)
    d (reference_dimension_ge_fourteen r c U i₀ j₀) hd.1 hd.2.1 hd.2.2
    (reference_row_padding r c U (d^12) B i₀ j₀ x)
    (reference_column_padding r c U (d^12) B i₀ j₀ x) hD

end ContingencyTables.SmallGraphProfiles

end OAI
