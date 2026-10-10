import OAI.Combinatorics.ContingencyTables.Transport.BalancedCompletionMass

namespace OAI

/-! # Recover the unique balanced joint object from its full padded table -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open PhysicalCompletionFibres FirstPaperPhysicalMarginal FirstPaperProfiles
open SmallContextFibres SmallContextCoordinates SmallContextEnumeration RowMajorEnumeration
open PaddedCompletions CompletionCounts

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

noncomputable def tableWord (small : I → J → Bool) (U : ℕ) (Y : I → J → ℕ)
    (hY : ∀ i j,small i j=true → Y i j ≤ U) :
    Fin (Fintype.card (Cells small)) → Fin (U+1) :=
  (wordChoices small U).symm (fun a => ⟨Y a.val.1 a.val.2,Nat.lt_succ_of_le (hY _ _ a.property)⟩)

lemma tableWord_false (small : I → J → Bool) (U : ℕ) (Y : I → J → ℕ)
    (hY : ∀ i j,small i j=true → Y i j ≤ U) (a : Cells small) :
    rawChoice small U (wordChoices small U (tableWord small U Y hY)) (a,false)=Y a.val.1 a.val.2 := by
  unfold tableWord
  rw [Equiv.apply_symm_apply]
  rfl

lemma tableWord_true (small : I → J → Bool) (U : ℕ) (Y : I → J → ℕ)
    (hY : ∀ i j,small i j=true → Y i j ≤ U) (a : Cells small) :
    rawChoice small U (wordChoices small U (tableWord small U Y hY)) (a,true)=U-Y a.val.1 a.val.2 := by
  unfold tableWord
  rw [Equiv.apply_symm_apply]
  rfl

/-- Residual feasibility and the literal small-cell bound suffice to
construct the balanced profile together with every retained large entry. -/
noncomputable def jointOfTable (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L U : ℕ)
    (hB : ∀ i j,small i j=true → B i j=U)
    (Y : Table (fun i => r i+rowLargeCount small i*L) (fun j => c j+columnLargeCount small j*L))
    (hY : ∀ i j,small i j=true → Y.val i j ≤ U)
    (hR : ∀ i,smallRow small Y.val i ≤ r i)
    (hC : ∀ j,smallColumnView small Y.val j ≤ c j)
    (hlarge : ∀ i j,small i j=false → Y.val i j ≤ B i j) : BalancedJoint small B r c L U :=
  ⟨tableWord small U Y.val hY,
    ⟨⟨(Y.val,Y.val),Y.property⟩,hR,hC,by
      intro i j hs
      constructor
      · exact (tableWord_false small U Y.val hY ⟨(i,j),hs⟩).symm
      · rw [tableWord_true,hB i j hs,Nat.sub_sub_self (hY i j hs)]
    ,fun _ _ _ => rfl,hlarge⟩⟩

lemma jointOfTable_projection (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L U : ℕ)
    (hB : ∀ i j,small i j=true → B i j=U)
    (Y : Table (fun i => r i+rowLargeCount small i*L) (fun j => c j+columnLargeCount small j*L))
    (hY : ∀ i j,small i j=true → Y.val i j ≤ U)
    (hR : ∀ i,smallRow small Y.val i ≤ r i)
    (hC : ∀ j,smallColumnView small Y.val j ≤ c j)
    (hlarge : ∀ i j,small i j=false → Y.val i j ≤ B i j) :
    balancedJointTable small B r c L U hB (jointOfTable small B r c L U hB Y hY hR hC hlarge)=Y := by
  apply Subtype.ext
  rfl

end ContingencyTables.SmallGraphProfiles

end OAI
