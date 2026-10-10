import OAI.Combinatorics.ContingencyTables.Transport.BalancedPhysicalPartition
import OAI.Combinatorics.ContingencyTables.Rooted.TreeMarginalEnumeration
import OAI.Combinatorics.ContingencyTables.Transport.TransversalCount

namespace OAI

/-! # The actual companion normalizer equals the full physical balanced mass -/

namespace ContingencyTables.CompanionPhysicalNormalizer

open scoped BigOperators Classical
open CommonBasesFPRAS CompanionFactorialApplication TwoLiftStates
open BalancedCellFibres PhysicalLargeProfiles LargePairEnumeration TreeMarginalSignature
open ForestPenaltyApplication ForestCountIdentification

private lemma finite_sum_congr {C : Type*} (F G : Fintype C) (f g : C → ℝ)
    (h : ∀ c,f c=g c) :
    @Finset.sum C ℝ _ (@Finset.univ C F) f=@Finset.sum C ℝ _ (@Finset.univ C G) g := by
  have he : F=G := Subsingleton.elim _ _
  cases he
  exact Finset.sum_congr rfl (fun c _ => h c)

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def physicalMass (A : Instance I J) (alpha : ℝ) : ℝ :=
  ∑ a : Profiles (cellWidth A),physicalWeight A.T A.b
    (ForestLiteralCount.lower A.T A.d A.b) (ForestLiteralCount.width A.T A.d A.b) A.r A.c alpha
    (BalancedCellFibres.profile (cellWidth A) a)

lemma small_width (A : Instance I J) (s : SmallCell A) :
    cellWidth A s.val=A.b s.val.1 s.val.2 := by
  have ht : ¬A.T.Adj (.inl s.val.1) (.inr s.val.2) := by
    intro ht
    have hs : A.small s.val.1 s.val.2=false := A.hTG ht
    exact Bool.false_ne_true (hs.symm.trans s.property)
  simp only [cellWidth,ForestLiteralCount.width,ht,ite_false]

noncomputable def smallInterval (A : Instance I J) (s : SmallCell A) :
    Fin (cellWidth A s.val+1) ≃ Fin (A.b s.val.1 s.val.2+1) where
  toFun k := ⟨k.val,by rw [← small_width A s]; exact k.isLt⟩
  invFun k := ⟨k.val,by rw [small_width A s]; exact k.isLt⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def smallProfilesEquiv (A : Instance I J) :
    SmallProfiles (fun a : I×J => A.small a.1 a.2) (cellWidth A) ≃
      TransversalCount.Profile (fun s : SmallCell A => A.b s.val.1 s.val.2) :=
  Equiv.piCongrRight (smallInterval A)

lemma small_display_eq (A : Instance I J)
    (s : SmallProfiles (fun a : I×J => A.small a.1 a.2) (cellWidth A)) :
    smallDisplay (fun a : I×J => A.small a.1 a.2) (cellWidth A) s=
      TransversalCount.display (fun s : SmallCell A => A.b s.val.1 s.val.2) (smallProfilesEquiv A s) := by
  funext u
  rcases u with ⟨a,b⟩
  cases b
  · rfl
  · change cellWidth A a.val-(s a).val=A.b a.val.1 a.val.2-(s a).val
    exact congrArg (fun n : ℕ => n-(s a).val) (small_width A a)

lemma h_eq_physical_sum (A : Instance I J) (alpha : ℝ) (z : View A → ℕ)
    (hz : BalancedBox.InBox (bounds A) z) :
    h A alpha z=
      ∑ a : PhysicalAssignments (fun a : I×J => A.small a.1 a.2) (cellWidth A),
        physicalWeight A.T A.b (ForestLiteralCount.lower A.T A.d A.b)
          (ForestLiteralCount.width A.T A.d A.b) A.r A.c alpha
          (physicalProfile (fun a : I×J => A.small a.1 a.2) (cellWidth A) z a) := by
  let e := (Fintype.equivFin (LargeCell (fun a : I×J => A.small a.1 a.2))).symm
  have hh := sourceMarginal_eq_largeMarginal A.small A.b A.T A.hTG A.hT A.hmax A.r A.c A.X
    A.d A.W alpha A.hd A.hcard A.hlarge A.hsmall A.hX A.hXr A.hXc e z hz
  change h A alpha z=_ at hh
  rw [hh]
  unfold ForestLargeMarginal.largeMarginal
  convert sum_joined_eq_physical (fun a : I×J => A.small a.1 a.2) (cellWidth A) e z
    (physicalWeight A.T A.b (ForestLiteralCount.lower A.T A.d A.b)
      (ForestLiteralCount.width A.T A.d A.b) A.r A.c alpha) using 1
  all_goals
    apply finite_sum_congr
    intro a
    rfl

lemma physicalMass_eq_split (A : Instance I J) (alpha : ℝ) :
    physicalMass A alpha=
      ∑ s : SmallProfiles (fun a : I×J => A.small a.1 a.2) (cellWidth A),
        ∑ a : PhysicalAssignments (fun a : I×J => A.small a.1 a.2) (cellWidth A),
          physicalWeight A.T A.b (ForestLiteralCount.lower A.T A.d A.b)
            (ForestLiteralCount.width A.T A.d A.b) A.r A.c alpha
            (physicalProfile (fun a : I×J => A.small a.1 a.2) (cellWidth A)
              (smallDisplay (fun a : I×J => A.small a.1 a.2) (cellWidth A) s) a) := by
  let F := physicalWeight A.T A.b (ForestLiteralCount.lower A.T A.d A.b)
    (ForestLiteralCount.width A.T A.d A.b) A.r A.c alpha
  let small : I×J → Bool := fun a => A.small a.1 a.2
  change (∑ a : Profiles (cellWidth A),F (BalancedCellFibres.profile (cellWidth A) a))=
    ∑ s : SmallProfiles small (cellWidth A),∑ a : PhysicalAssignments small (cellWidth A),
      F (physicalProfile small (cellWidth A) (smallDisplay small (cellWidth A) s) a)
  have he := Fintype.sum_equiv (partition small (cellWidth A))
    (fun a => F (BalancedCellFibres.profile (cellWidth A) a))
    (fun a => F (physicalProfile small (cellWidth A) (smallDisplay small (cellWidth A) a.1) a.2))
    (by
      intro a
      have hh := partition_profile small (cellWidth A) ((partition small (cellWidth A)) a)
      simpa only [Equiv.symm_apply_apply] using congrArg F hh)
  rw [he,Fintype.sum_prod_type]

/-- Exact cancellation and actual small/large product partition identify
the manuscript's normalizer with the physical mass used in the terminal
root and tree contamination estimates. -/
theorem normalizer_eq_physical_mass (A : Instance I J) (alpha : ℝ) :
    slotTotal pairs (f A alpha) ∅=physicalMass A alpha := by
  rw [CompanionTransversalCount.total_eq_raw_profiles]
  rw [physicalMass_eq_split]
  symm
  apply Fintype.sum_equiv (smallProfilesEquiv A)
  intro s
  rw [small_display_eq]
  symm
  apply h_eq_physical_sum
  intro u
  rcases u with ⟨a,b⟩
  cases b
  · exact Nat.le_of_lt_succ ((smallProfilesEquiv A s) a).isLt
  · exact Nat.sub_le _ _

end ContingencyTables.CompanionPhysicalNormalizer

end OAI
