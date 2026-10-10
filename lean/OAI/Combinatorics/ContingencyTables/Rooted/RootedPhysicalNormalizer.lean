import OAI.Combinatorics.ContingencyTables.Rooted.RootedFactorialApplication
import OAI.Combinatorics.ContingencyTables.Counting.CompanionPhysicalNormalizer

namespace OAI

/-! # The selected-root factorial normalizer is the literal physical mass -/

namespace ContingencyTables.RootedPhysicalNormalizer

open scoped BigOperators Classical
open CommonBasesFPRAS CompanionFactorialApplication TwoLiftStates RootedFactorialApplication
open BalancedCellFibres PhysicalLargeProfiles LargePairEnumeration TreeMarginalSignature
open CompanionPhysicalNormalizer (smallProfilesEquiv small_display_eq)

private lemma finite_sum_congr {C : Type*} (F G : Fintype C) (f g : C → ℝ)
    (h : ∀ c,f c=g c) :
    @Finset.sum C ℝ _ (@Finset.univ C F) f=@Finset.sum C ℝ _ (@Finset.univ C G) g := by
  have he : F=G := Subsingleton.elim _ _
  cases he
  exact Finset.sum_congr rfl (fun c _ => h c)

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def physicalMass (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha : ℝ) : ℝ :=
  ∑ a : Profiles (cellWidth A),RootedPenalty.physicalWeight A R alpha
    (BalancedCellFibres.profile (cellWidth A) a)

lemma h_eq_physical_sum (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (alpha : ℝ) (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z) :
    RootedCountIdentification.h A R alpha z=
      ∑ a : PhysicalAssignments (fun a : I×J => A.small a.1 a.2) (cellWidth A),
        RootedPenalty.physicalWeight A R alpha
          (physicalProfile (fun a : I×J => A.small a.1 a.2) (cellWidth A) z a) := by
  let e := (Fintype.equivFin (LargeCell (fun a : I×J => A.small a.1 a.2))).symm
  rw [RootedCountIdentification.h_eq_largeMarginal A R alpha e z hz]
  unfold RootedLargeMarginal.largeMarginal
  convert sum_joined_eq_physical (fun a : I×J => A.small a.1 a.2) (cellWidth A) e z
    (RootedPenalty.physicalWeight A R alpha) using 1
  all_goals
    apply finite_sum_congr
    intro a
    rfl

lemma physicalMass_eq_split (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha : ℝ) :
    physicalMass A R alpha=
      ∑ s : SmallProfiles (fun a : I×J => A.small a.1 a.2) (cellWidth A),
        ∑ a : PhysicalAssignments (fun a : I×J => A.small a.1 a.2) (cellWidth A),
          RootedPenalty.physicalWeight A R alpha
            (physicalProfile (fun a : I×J => A.small a.1 a.2) (cellWidth A)
              (smallDisplay (fun a : I×J => A.small a.1 a.2) (cellWidth A) s) a) := by
  let F := RootedPenalty.physicalWeight A R alpha
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

lemma total_eq_raw_profiles (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha : ℝ) :
    slotTotal pairs (RootedFactorialApplication.f A R alpha) ∅=
      ∑ x : TransversalCount.Profile (fun s : SmallCell A => A.b s.val.1 s.val.2),
        RootedCountIdentification.h A R alpha
          (TransversalCount.display (fun s : SmallCell A => A.b s.val.1 s.val.2) x) := by
  unfold RootedFactorialApplication.f
  rw [CompanionInitialization.denominator_eq]
  convert TransversalCount.slotTotal_eq_profiles
    (fun s : SmallCell A => A.b s.val.1 s.val.2) (RootedCountIdentification.h A R alpha) using 1
  congr 1
  all_goals
    congr 1
    ext
    simp

/-- Factorial cancellation and the actual physical partition identify
this selected-root normalizer with the mass used in terminal estimates. -/
theorem normalizer_eq_physical_mass (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha : ℝ) :
    slotTotal pairs (RootedFactorialApplication.f A R alpha) ∅=physicalMass A R alpha := by
  rw [total_eq_raw_profiles,physicalMass_eq_split]
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

end ContingencyTables.RootedPhysicalNormalizer

end OAI
