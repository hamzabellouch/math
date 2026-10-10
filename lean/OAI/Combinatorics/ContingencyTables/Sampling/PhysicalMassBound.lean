import OAI.Combinatorics.ContingencyTables.Sampling.PhysicalResidualMargins

namespace OAI

/-! # Count the small state and its large completion jointly -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open PhysicalCompletionFibres PhysicalLargeProfiles FirstPaperPhysicalMarginal
open SmallContextFibres LargePairEnumeration CompletionCounts NestedPenaltyApplication

universe u
variable {I J : Type u} [Fintype I] [Fintype J]

lemma hardMarginal_le_assignments (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (z : SmallProfile small) :
    hardMarginal small B r c L z ≤
      (Fintype.card (PhysicalAssignments (fun a : I×J => small a.1 a.2)
        (fun a => B a.1 a.2)):ℝ) := by
  unfold hardMarginal fullHardFamily hardWeight
  rw [Finset.sum_boole,← Fintype.card_subtype]
  exact_mod_cast Fintype.card_subtype_le _

lemma boundedProfile_card_le (small : I → J → Bool) (B : I → J → ℕ)
    (C : ℕ) (hB : ∀ i j,B i j ≤ C) :
    Fintype.card (BoundedProfile small B) ≤
      (C+1)^Fintype.card (SmallView (fun a : I×J => small a.1 a.2)) := by
  change Fintype.card ((a : SmallView (fun a : I×J => small a.1 a.2)) →
    Fin (B a.1.val.1 a.1.val.2+1)) ≤ _
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin]
  calc
    _ ≤ ∏ _a : SmallView (fun a : I×J => small a.1 a.2),(C+1) :=
      Finset.prod_le_prod (fun a _ => Nat.add_le_add_right (hB _ _) 1)
    _ = _ := by simp

lemma physicalAssignments_card_le (small : I → J → Bool) (B : I → J → ℕ)
    (C : ℕ) (hB : ∀ i j,B i j ≤ C) :
    Fintype.card (PhysicalAssignments (fun a : I×J => small a.1 a.2) (fun a => B a.1 a.2)) ≤
      (C+1)^Fintype.card (LargeCell (fun a : I×J => small a.1 a.2)) := by
  unfold PhysicalAssignments
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin]
  calc
    _ ≤ ∏ _a : LargeCell (fun a : I×J => small a.1 a.2),(C+1) :=
      Finset.prod_le_prod (fun a _ => Nat.add_le_add_right (hB _ _) 1)
    _ = _ := by simp

variable [LinearOrder I] [LinearOrder J]

theorem physical_total_mass_le (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L C : ℕ) (hB : ∀ i j,B i j ≤ C) :
    (∑ z : PhysicalStates small B r c L,hardMarginal small B r c L
      (physicalProfile small B r c L z)) ≤
      ((C+1:ℕ):ℝ)^(2*dimensionAllowance (I := I) (J := J)) := by
  let s := Fintype.card (SmallView (fun a : I×J => small a.1 a.2))
  let l := Fintype.card (LargeCell (fun a : I×J => small a.1 a.2))
  have hs : Fintype.card (PhysicalStates small B r c L) ≤ (C+1)^s :=
    (Fintype.card_subtype_le _).trans
      ((Fintype.card_subtype_le _).trans (by
        simpa only [s,Fintype.card_eq_nat_card] using boundedProfile_card_le small B C hB))
  have hl : Nat.card (PhysicalAssignments (fun a : I×J => small a.1 a.2)
      (fun a => B a.1 a.2)) ≤ (C+1)^l := by
    simpa only [l,Fintype.card_eq_nat_card] using physicalAssignments_card_le small B C hB
  have he := Fintype.card_congr (partitionEquiv (fun a : I×J => small a.1 a.2))
  simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_bool] at he
  have hexp : s+l ≤ 2*dimensionAllowance (I := I) (J := J) := by
    simp only [s,l,Fintype.card_prod,Fintype.card_bool]
    nlinarith [dimension_le_allowance (I := I) (J := J)]
  have hbound (z : PhysicalStates small B r c L) : hardMarginal small B r c L
      (physicalProfile small B r c L z) ≤ (Nat.card (PhysicalAssignments
        (fun a : I×J => small a.1 a.2) (fun a => B a.1 a.2)):ℝ) := by
    simpa only [Fintype.card_eq_nat_card] using hardMarginal_le_assignments small B r c L
      (physicalProfile small B r c L z)
  calc
    _ ≤ ∑ _z : PhysicalStates small B r c L,
        (Nat.card (PhysicalAssignments (fun a : I×J => small a.1 a.2)
          (fun a => B a.1 a.2)):ℝ) :=
      Finset.sum_le_sum (fun z _ => hbound z)
    _ = (Fintype.card (PhysicalStates small B r c L):ℝ)*
        Nat.card (PhysicalAssignments (fun a : I×J => small a.1 a.2) (fun a => B a.1 a.2)) := by simp
    _ ≤ ((C+1:ℕ):ℝ)^s*((C+1:ℕ):ℝ)^l := by
      apply mul_le_mul
      · exact_mod_cast hs
      · exact_mod_cast hl
      · positivity
      · positivity
    _ = ((C+1:ℕ):ℝ)^(s+l) := (pow_add _ _ _).symm
    _ ≤ _ := by
      exact_mod_cast Nat.pow_le_pow_right (show 1 ≤ C+1 by omega) hexp

end ContingencyTables.SmallGraphProfiles

end OAI
