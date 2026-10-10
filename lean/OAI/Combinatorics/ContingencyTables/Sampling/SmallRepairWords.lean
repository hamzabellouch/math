import OAI.Combinatorics.ContingencyTables.Sampling.PhysicalRepairMass
import OAI.Combinatorics.ContingencyTables.Transport.WordContextVariance

namespace OAI

/-! # Actual positive defects repair to the physical transversal words -/

namespace ContingencyTables.SmallGraphProfiles

open scoped Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles
open FirstPaperPhysicalMarginal PaddedCompletions CompletionCounts
open SmallContextEnumeration RowMajorEnumeration

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

def PositiveDefects (small : I → J → Bool) (B : I → J → ℕ) (r : I → ℕ) (c : J → ℕ) (L : ℕ) :=
  {z : BoundedProfile small B // SingleDefect small B (naturalProfile z) ∧
    0 < hardMarginal small B r c L (naturalProfile z)}

noncomputable instance positiveDefectsFintype (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) : Fintype (PositiveDefects small B r c L) := by
  unfold PositiveDefects
  infer_instance

lemma defect_labels_exist (small : I → J → Bool) (B : I → J → ℕ) (r : I → ℕ) (c : J → ℕ) (L : ℕ)
    (z : PositiveDefects small B r c L) :
    ∃ st : Cells small×Cells small,IsDefect (smallView small (naturalProfile z.val) false)
      (smallQ small B (naturalProfile z.val)) st.1.val st.2.val := by
  obtain ⟨s,t,hs,ht,hd⟩ := z.property.1
  exact ⟨(⟨s,hs⟩,⟨t,ht⟩),hd⟩

noncomputable def defectLabels (small : I → J → Bool) (B : I → J → ℕ) (r : I → ℕ) (c : J → ℕ) (L : ℕ)
    (z : PositiveDefects small B r c L) : Cells small×Cells small :=
  Classical.choose (defect_labels_exist small B r c L z)

lemma defectLabels_spec (small : I → J → Bool) (B : I → J → ℕ) (r : I → ℕ) (c : J → ℕ) (L : ℕ)
    (z : PositiveDefects small B r c L) :
    IsDefect (smallView small (naturalProfile z.val) false) (smallQ small B (naturalProfile z.val))
      (defectLabels small B r c L z).1.val (defectLabels small B r c L z).2.val :=
  Classical.choose_spec (defect_labels_exist small B r c L z)

noncomputable def repairWord (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U)
    (z : PositiveDefects (firstPaperSmall r c U) B r c L) :
    Fin (Fintype.card (Cells (firstPaperSmall r c U))) → Fin (U+1) := fun j =>
  let st := defectLabels _ B r c L z
  let a := enumeration (firstPaperSmall r c U) j
  ⟨repairMatrix (smallView (firstPaperSmall r c U) (naturalProfile z.val) false)
      st.1.val st.2.val a.val.1 a.val.2,Nat.lt_succ_of_le (by
    exact (repair_small_capacity r c U L B hB (naturalProfile z.val)
      (naturalProfile_bounded z.val) st.1.val st.2.val st.1.property st.2.property
      (defectLabels_spec _ B r c L z) z.property.2 a).trans_eq (hB _ _ a.property))⟩

lemma repairWord_profile (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U)
    (z : PositiveDefects (firstPaperSmall r c U) B r c L) :
    rawChoice (firstPaperSmall r c U) U
      (wordChoices (firstPaperSmall r c U) U (repairWord r c U L B hB z))=
      repairedProfile (firstPaperSmall r c U) B (naturalProfile z.val)
        (defectLabels _ B r c L z).1.val (defectLabels _ B r c L z).2.val := by
  funext p
  rcases p with ⟨a,b⟩
  have he : (wordChoices (firstPaperSmall r c U) U (repairWord r c U L B hB z) a).val=
      repairMatrix (smallView (firstPaperSmall r c U) (naturalProfile z.val) false)
        (defectLabels _ B r c L z).1.val (defectLabels _ B r c L z).2.val a.val.1 a.val.2 := by
    change repairMatrix (smallView (firstPaperSmall r c U) (naturalProfile z.val) false)
      (defectLabels _ B r c L z).1.val (defectLabels _ B r c L z).2.val
      (enumeration (firstPaperSmall r c U) ((enumeration (firstPaperSmall r c U)).symm a)).val.1
      (enumeration (firstPaperSmall r c U) ((enumeration (firstPaperSmall r c U)).symm a)).val.2=_
    rw [Equiv.apply_symm_apply]
  cases b
  · exact he
  · change U-_ = B a.val.1 a.val.2-_
    rw [he,hB _ _ a.property]

theorem repairWord_weight (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U)
    (hcap : ∀ T : ResidualTables (firstPaperSmall r c U) r c
      (fun i => r i+rowLargeCount (firstPaperSmall r c U) i*L)
      (fun j => c j+columnLargeCount (firstPaperSmall r c U) j*L),∀ i j,T.val.val i j ≤ B i j)
    (z : PositiveDefects (firstPaperSmall r c U) B r c L) :
    hardMarginal (firstPaperSmall r c U) B r c L (naturalProfile z.val) ≤
      wordWeight (firstPaperSmall r c U) B r c L U (repairWord r c U L B hB z) := by
  unfold wordWeight
  rw [repairWord_profile]
  exact physical_repair_weight_le r c U L B hB (naturalProfile z.val) (naturalProfile_bounded z.val)
    _ _ (defectLabels _ B r c L z).1.property (defectLabels _ B r c L z).2.property
    (defectLabels_spec _ B r c L z) hcap z.property.2

theorem repairWord_type_injective (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U) :
    Function.Injective (fun z : PositiveDefects (firstPaperSmall r c U) B r c L =>
      (defectLabels _ B r c L z,repairWord r c U L B hB z)) := by
  intro x y he
  have hl := congrArg Prod.fst he
  dsimp only at hl
  have hr := congrArg (fun a => rawChoice (firstPaperSmall r c U) U
    (wordChoices (firstPaperSmall r c U) U a)) (congrArg Prod.snd he)
  rw [repairWord_profile,repairWord_profile,hl] at hr
  have hdx := defectLabels_spec (firstPaperSmall r c U) B r c L x
  rw [hl] at hdx
  apply Subtype.ext
  apply naturalProfile_injective (firstPaperSmall r c U) B
  exact repairedProfile_injective (firstPaperSmall r c U) B _ _ _ _
    (naturalProfile_bounded x.val) (naturalProfile_bounded y.val) hdx
    (defectLabels_spec _ B r c L y) hr

end ContingencyTables.SmallGraphProfiles

end OAI
