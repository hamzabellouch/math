import OAI.Combinatorics.ContingencyTables.Sampling.SmallBalancedEncoding

namespace OAI

/-! # Balanced profile/completion pairs inject into padded tables -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open PhysicalCompletionFibres FirstPaperPhysicalMarginal FirstPaperProfiles
open SmallContextFibres SmallContextCoordinates SmallContextEnumeration RowMajorEnumeration
open PaddedCompletions CompletionCounts

universe u
variable {I J : Type u} [Fintype I] [Fintype J]

lemma balanced_fibre_views_eq (small : I → J → Bool) (B : I → J → ℕ)
    (r rbar : I → ℕ) (c cbar : J → ℕ) (z : SmallProfile small)
    (hz : Balanced small B z) (Z : CompletionFibre small B r rbar c cbar z) :
    Z.val.val.1=Z.val.val.2 := by
  funext i j
  cases hs : small i j with
  | false => exact Z.property.2.2.2.1 i j hs
  | true =>
    rw [(Z.property.2.2.1 i j hs).1,(Z.property.2.2.1 i j hs).2]
    have h := hz i j
    simpa only [smallView,smallQ,hs,dite_eq_left] using h

noncomputable def balancedFibreTable (small : I → J → Bool) (B : I → J → ℕ)
    (r rbar : I → ℕ) (c cbar : J → ℕ) (z : SmallProfile small)
    (hz : Balanced small B z) (Z : CompletionFibre small B r rbar c cbar z) :
    Table rbar cbar :=
  ⟨Z.val.val.1,Z.val.property.1,by
    rw [balanced_fibre_views_eq small B r rbar c cbar z hz Z]
    exact Z.val.property.2⟩

variable [LinearOrder I] [LinearOrder J]

abbrev BalancedJoint (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L U : ℕ) :=
  (a : Fin (Fintype.card (Cells small)) → Fin (U+1)) ×
    CompletionFibre small B r (fun i => r i+rowLargeCount small i*L)
      c (fun j => c j+columnLargeCount small j*L) (rawChoice small U (wordChoices small U a))

noncomputable def balancedJointTable (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L U : ℕ)
    (hB : ∀ i j,small i j=true → B i j=U) (a : BalancedJoint small B r c L U) :
    Table (fun i => r i+rowLargeCount small i*L) (fun j => c j+columnLargeCount small j*L) :=
  balancedFibreTable small B r _ c _ _ (rawChoice_balanced small B U hB _) a.2

lemma balancedJointTable_injective (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L U : ℕ)
    (hB : ∀ i j,small i j=true → B i j=U) :
    Function.Injective (balancedJointTable small B r c L U hB) := by
  intro a b hab
  apply fibre_projection_injective small B r _ c _
    (fun a => rawChoice small U (wordChoices small U a))
    ((rawChoice_injective small U).comp (wordChoices small U).injective)
    (fun a => rawChoice_bounded small B U hB _) 
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg Subtype.val hab
  · have ha := balanced_fibre_views_eq small B r _ c _ _ (rawChoice_balanced small B U hB _) a.2
    have hb := balanced_fibre_views_eq small B r _ c _ _ (rawChoice_balanced small B U hB _) b.2
    rw [← ha,← hb]
    exact congrArg Subtype.val hab

lemma word_mass_eq_balancedJoint_card (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L U : ℕ)
    (hB : ∀ i j,small i j=true → B i j=U) :
    (∑ a,wordWeight small B r c L U a)=(Fintype.card (BalancedJoint small B r c L U):ℝ) := by
  rw [Fintype.card_sigma,Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact hardMarginal_eq_fibre_card small B r c L _ (rawChoice_bounded small B U hB _)

/-- This inequality retains all large-cell multiplicities and counts every
balanced word exactly once. -/
theorem word_mass_le_padded_count (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L U : ℕ)
    (hB : ∀ i j,small i j=true → B i j=U) :
    (∑ a,wordWeight small B r c L U a) ≤
      (Fintype.card (Table (fun i => r i+rowLargeCount small i*L)
        (fun j => c j+columnLargeCount small j*L)):ℝ) := by
  rw [word_mass_eq_balancedJoint_card small B r c L U hB]
  exact_mod_cast Fintype.card_le_of_injective _ (balancedJointTable_injective small B r c L U hB)

end ContingencyTables.SmallGraphProfiles

end OAI
