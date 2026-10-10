import OAI.Combinatorics.ContingencyTables.Sampling.SmallRepairWords
import OAI.Combinatorics.ContingencyTables.Transport.RawSmallChoiceProperties
import OAI.Combinatorics.ContingencyTables.Transport.FiniteSymmetricEnergy

namespace OAI

/-! # The actual small graph contains its exchanges and designated repairs -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles
open FirstPaperPhysicalMarginal PaddedCompletions CompletionCounts
open SmallContextEnumeration RowMajorEnumeration IntegerWeightedTransport

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

noncomputable def repairEdges (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U) :
    Finset (SmallProfile (firstPaperSmall r c U)×SmallProfile (firstPaperSmall r c U)) :=
  let target := fun z => rawChoice (firstPaperSmall r c U) U
    (wordChoices (firstPaperSmall r c U) U (repairWord r c U L B hB z))
  (Finset.univ.image (fun z : PositiveDefects (firstPaperSmall r c U) B r c L =>
    (naturalProfile z.val,target z))) ∪
  (Finset.univ.image (fun z : PositiveDefects (firstPaperSmall r c U) B r c L =>
    (target z,naturalProfile z.val)))

noncomputable def fullEdges (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U) :=
  physicalEdges (firstPaperSmall r c U) B ∪ repairEdges r c U L B hB

noncomputable def fullEnergy (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U)
    (H : SmallProfile (firstPaperSmall r c U) → ℝ) : ℝ :=
  symmetricEnergy (fullEdges r c U L B hB) (hardMarginal (firstPaperSmall r c U) B r c L) H

lemma physicalEnergy_le_full (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U)
    (H : SmallProfile (firstPaperSmall r c U) → ℝ) :
    physicalEnergy (firstPaperSmall r c U) B (hardMarginal (firstPaperSmall r c U) B r c L) H ≤
      fullEnergy r c U L B hB H :=
  symmetricEnergy_mono _ _ Finset.subset_union_left _ _ (hardMarginal_nonnegative _ _ _ _ _)

lemma fullEnergy_nonnegative (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U)
    (H : SmallProfile (firstPaperSmall r c U) → ℝ) : 0 ≤ fullEnergy r c U L B hB H := by
  unfold fullEnergy symmetricEnergy
  exact div_nonneg (Finset.sum_nonneg (fun p _ => pairTerm_nonnegative _ _
    (hardMarginal_nonnegative _ _ _ _ _) p)) (by norm_num)

theorem actual_repair_energy_le (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U)
    (hcap : ∀ T : ResidualTables (firstPaperSmall r c U) r c
      (fun i => r i+rowLargeCount (firstPaperSmall r c U) i*L)
      (fun j => c j+columnLargeCount (firstPaperSmall r c U) j*L),∀ i j,T.val.val i j ≤ B i j)
    (H : SmallProfile (firstPaperSmall r c U) → ℝ) :
    (∑ z : PositiveDefects (firstPaperSmall r c U) B r c L,
      hardMarginal (firstPaperSmall r c U) B r c L (naturalProfile z.val)*
        (H (naturalProfile z.val)-wordObservable (firstPaperSmall r c U) U H (repairWord r c U L B hB z))^2) ≤
      fullEnergy r c U L B hB H := by
  let x := fun z : PositiveDefects (firstPaperSmall r c U) B r c L => naturalProfile z.val
  let y := fun z : PositiveDefects (firstPaperSmall r c U) B r c L =>
    rawChoice (firstPaperSmall r c U) U (wordChoices (firstPaperSmall r c U) U (repairWord r c U L B hB z))
  have hx : Function.Injective x := by
    intro a b he
    apply Subtype.ext
    exact naturalProfile_injective _ B he
  have hxy : ∀ a b,x a≠y b := by
    intro a b he
    have hb := rawChoice_balanced (firstPaperSmall r c U) B U hB
      (wordChoices (firstPaperSmall r c U) U (repairWord r c U L B hB b))
    have hdef := a.property.1
    change SingleDefect _ B (x a) at hdef
    rw [he] at hdef
    exact balanced_not_defect _ B _ hb hdef
  have he := repair_energy_le (fullEdges r c U L B hB)
    (hardMarginal (firstPaperSmall r c U) B r c L) H (hardMarginal_nonnegative _ _ _ _ _) x y hx hxy
    (fun z => Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨z,Finset.mem_univ _,rfl⟩)))
    (fun z => Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨z,Finset.mem_univ _,rfl⟩)))
  have hterm (z : PositiveDefects (firstPaperSmall r c U) B r c L) :
      pairTerm (hardMarginal (firstPaperSmall r c U) B r c L) H (x z,y z)=
        hardMarginal (firstPaperSmall r c U) B r c L (naturalProfile z.val)*
          (H (naturalProfile z.val)-wordObservable (firstPaperSmall r c U) U H (repairWord r c U L B hB z))^2 := by
    change min (hardMarginal (firstPaperSmall r c U) B r c L (naturalProfile z.val))
      (wordWeight (firstPaperSmall r c U) B r c L U (repairWord r c U L B hB z)) *
      (H (naturalProfile z.val)-wordObservable (firstPaperSmall r c U) U H
        (repairWord r c U L B hB z))^2 = _
    rw [min_eq_left (repairWord_weight r c U L B hB hcap z)]
  simp_rw [hterm] at he
  exact he

end ContingencyTables.SmallGraphProfiles

end OAI
