import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperSmallMixing
import OAI.Combinatorics.ContingencyTables.Sampling.SmallProfileEncoding

namespace OAI

/-! # Completion-retaining repair bounds the stationary normalizer -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles
open FirstPaperPhysicalMarginal PaddedCompletions CompletionCounts
open SmallContextEnumeration RowMajorEnumeration FiniteExposureVariance

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

lemma physical_mass_eq_profiles (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) :
    (∑ z : PhysicalStates small B r c L,hardMarginal small B r c L
      (physicalProfile small B r c L z))=
      ∑ z : Profiles small B,hardMarginal small B r c L (naturalProfile z.val) := by
  apply Fintype.sum_of_injective Subtype.val Subtype.val_injective
  · intro z hz
    have hn : ¬0 < hardMarginal small B r c L (naturalProfile z.val) := by
      intro hp
      exact hz ⟨⟨z,hp⟩,rfl⟩
    exact le_antisymm (le_of_not_gt hn) (hardMarginal_nonnegative _ _ _ _ _ _)
  · intro z
    rfl

lemma physical_mass_eq_words_defects (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L U : ℕ)
    (hB : ∀ i j,small i j=true → B i j=U) :
    (∑ z : PhysicalStates small B r c L,hardMarginal small B r c L
      (physicalProfile small B r c L z))=
      (∑ a,wordWeight small B r c L U a)+
      ∑ z : PositiveDefects small B r c L,hardMarginal small B r c L (naturalProfile z.val) := by
  rw [physical_mass_eq_profiles]
  have he := Fintype.sum_of_injective (encodeProfile small B r c L U hB)
    (encodeProfile_injective small B r c L U hB)
    (fun z => hardMarginal small B r c L (naturalProfile (encodeProfile small B r c L U hB z).val))
    (fun z => hardMarginal small B r c L (naturalProfile z.val))
    (outside_encoding_weight_zero small B r c L U hB) (fun _ => rfl)
  rw [← he,Fintype.sum_sum_type]
  rfl

/-- The repair preserves all completions and has at most one preimage per
ordered defect label. Thus defect mass costs at most |S| squared. -/
lemma defect_mass_le_words (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U)
    (hcap : ∀ T : ResidualTables (firstPaperSmall r c U) r c
      (fun i => r i+rowLargeCount (firstPaperSmall r c U) i*L)
      (fun j => c j+columnLargeCount (firstPaperSmall r c U) j*L),∀ i j,T.val.val i j ≤ B i j) :
    (∑ z : PositiveDefects (firstPaperSmall r c U) B r c L,
      hardMarginal (firstPaperSmall r c U) B r c L (naturalProfile z.val)) ≤
      (Fintype.card (Cells (firstPaperSmall r c U)×Cells (firstPaperSmall r c U)):ℝ)*
        ∑ a,wordWeight (firstPaperSmall r c U) B r c L U a := by
  have h := repair_center_mass (wordWeight (firstPaperSmall r c U) B r c L U)
    (fun z : PositiveDefects (firstPaperSmall r c U) B r c L =>
      hardMarginal (firstPaperSmall r c U) B r c L (naturalProfile z.val))
    (fun _ => (1:ℝ)) (repairWord r c U L B hB) (defectLabels _ B r c L)
    (fun _ => hardMarginal_nonnegative _ _ _ _ _ _)
    (repairWord_weight r c U L B hB hcap) (repairWord_type_injective r c U L B hB) 0
  simpa only [sub_zero,one_pow,mul_one] using h

/-- The normalizer of the actual small chain is bounded by balanced
completion mass times the manuscript's polynomial defect factor. -/
theorem state_mass_le_balanced (r : I → ℕ) (c : J → ℕ) :
    (∑ z,stateWeight r c z) ≤
      (1+(dimensionAllowance (I := I) (J := J):ℝ)^2)*
        ∑ a,wordWeight (paperSmall r c) (stateCapacity r c) r c
          ((dimensionAllowance (I := I) (J := J))^12)
          ((dimensionAllowance (I := I) (J := J))^20) a := by
  let d := dimensionAllowance (I := I) (J := J)
  let U := d^20
  let L := d^12
  let small := paperSmall r c
  let B := stateCapacity r c
  have hB : ∀ i j,small i j=true → B i j=U := stateCapacity_small r c
  have hcap := paper_residual_capacity r c d L U dimension_le_allowance
  have hmass := physical_mass_eq_words_defects small B r c L U hB
  have hdef := defect_mass_le_words r c U L B hB hcap
  have hq : Fintype.card (Cells small) ≤ d :=
    (small_card_le_dimension small).trans dimension_le_allowance
  have hT : (Fintype.card (Cells small×Cells small):ℝ) ≤ (d:ℝ)^2 := by
    exact_mod_cast (show Fintype.card (Cells small×Cells small) ≤ d^2 by
      simpa only [Fintype.card_prod,pow_two] using Nat.mul_le_mul hq hq)
  have hw : 0 ≤ ∑ a,wordWeight small B r c L U a :=
    Finset.sum_nonneg (fun _ _ => hardMarginal_nonnegative _ _ _ _ _ _)
  have hm := mul_le_mul_of_nonneg_right hT hw
  change (∑ z : PhysicalStates small B r c L,hardMarginal small B r c L
    (physicalProfile small B r c L z)) ≤ (1+(d:ℝ)^2)*∑ a,wordWeight small B r c L U a
  rw [hmass]
  linarith

end ContingencyTables.SmallGraphProfiles

end OAI
