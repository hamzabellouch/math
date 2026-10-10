import OAI.Combinatorics.ContingencyTables.Sampling.AllSmallFibres

namespace OAI

/-! # Reading the unique all-small completion directly from its profile -/

namespace ContingencyTables.SmallGraphProfiles
open scoped BigOperators Classical
open CompletionCounts PhysicalCompletionFibres PaddedCompletions

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
variable (r : I → ℕ) (c : J → ℕ)

/-- The output data consists only of the two stored small views. Existence
of a completion supplies the erased proof that these are valid margins. -/
noncomputable def allSmallFibre
    (hsmall : ∀ i j,FirstPaperPhysicalMarginal.paperSmall r c i j=true)
    (z : PaperStates r c) : PaperFibre r c z := by
  let p := SmallContextFibres.naturalProfile z.val.val
  let views := (fun i j => p (⟨(i,j),hsmall i j⟩,false),
    fun i j => stateCapacity r c i j-p (⟨(i,j),hsmall i j⟩,true))
  have hv : ∃ h, (⟨views,h⟩ : RowColumnPair
      (fun i => r i+PaddedCompletions.rowLargeCount (FirstPaperPhysicalMarginal.paperSmall r c) i*
        ((dimensionAllowance (I := I) (J := J))^12))
      (fun j => c j+PaddedCompletions.columnLargeCount (FirstPaperPhysicalMarginal.paperSmall r c) j*
        ((dimensionAllowance (I := I) (J := J))^12))).val=views := by
    obtain ⟨Z⟩ := (inferInstance : Nonempty (PaperFibre r c z))
    have he : views=Z.val.val := by
      apply Prod.ext
      · funext i j
        exact (Z.property.2.2.1 i j (hsmall i j)).1.symm
      · funext i j
        exact (Z.property.2.2.1 i j (hsmall i j)).2.symm
    exact ⟨by rw [he]; exact Z.val.property,rfl⟩
  let pair := (⟨views,hv.choose⟩ : RowColumnPair
      (fun i => r i+PaddedCompletions.rowLargeCount (FirstPaperPhysicalMarginal.paperSmall r c) i*
        ((dimensionAllowance (I := I) (J := J))^12))
      (fun j => c j+PaddedCompletions.columnLargeCount (FirstPaperPhysicalMarginal.paperSmall r c) j*
        ((dimensionAllowance (I := I) (J := J))^12)))
  refine ⟨pair,?_⟩
  obtain ⟨Z⟩ := (inferInstance : Nonempty (PaperFibre r c z))
  have he : pair=Z.val := by
    apply Subtype.ext
    apply Prod.ext
    · funext i j
      exact (Z.property.2.2.1 i j (hsmall i j)).1.symm
    · funext i j
      exact (Z.property.2.2.1 i j (hsmall i j)).2.symm
  exact he.symm ▸ Z.property

end ContingencyTables.SmallGraphProfiles

end OAI
