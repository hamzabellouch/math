import OAI.Combinatorics.ContingencyTables.Rooted.RootedLiteralCount
import OAI.Combinatorics.ContingencyTables.Rooted.RootedLargeMarginal

namespace OAI

/-! # The selected-root physical marginal is its literal completion count -/

namespace ContingencyTables.RootedCountIdentification

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion RootedPenalty RootedLiteralCount
open ForestCountIdentification ForestAssignmentSplit ForestLiteralCount
open PhysicalLargeProfiles LargePairEnumeration BalancedBox GraphCompletionCounts

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def h (A : Instance I J) (S : Selection A.T) (alpha : ℝ)
    (z : View A → ℕ) : ℝ :=
  ∑ f : FreeIndex A.small A.T A.b,
    (2:ℝ)^(-alpha*RootedLiteralCount.actualPenalty A S
      (smallX A.small z) (smallY A.small z) (freeTable A.small A.T A.b f)
      (RootedPhysicalCompletion.solved A S (fun i j => (smallX A.small z i j:ℤ))
        (fun i j => ((A.b i j-smallY A.small z i j:ℕ):ℤ))
        (fun i j => (freeTable A.small A.T A.b f i j:ℤ))))

theorem h_positive (A : Instance I J) (S : Selection A.T) (alpha : ℝ)
    (z : View A → ℕ) : 0<h A S alpha z := by
  let f : FreeIndex A.small A.T A.b := fun _ => 0
  unfold h
  apply lt_of_lt_of_le (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) _)
  exact Finset.single_le_sum (fun a _ =>
    (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) _).le) (Finset.mem_univ f)

theorem h_zero (A : Instance I J) (S : Selection A.T) (z : View A → ℕ) :
    h A S 0 z=∏ a : FreeCell A.small A.T,((A.b a.val.1 a.val.2+1:ℕ):ℝ) := by
  simp [h,Fintype.card_pi,Nat.cast_prod]

private theorem physical_sum_split (A : Instance I J) (z : View A → ℕ)
    (F : (((I×J)×Bool) → ℕ) → ℝ) :
    (∑ a : PhysicalAssignments (fun a : I×J => A.small a.1 a.2)
      (fun a => width A.T A.d A.b a.1 a.2),
      F (physicalProfile (fun a : I×J => A.small a.1 a.2)
        (fun a => width A.T A.d A.b a.1 a.2) z a))=
      ∑ f : FreeIndex A.small A.T A.b,∑ t : TreeIndex A.T A.d A.b,
        F (profile A.small A.T A.d A.b (smallX A.small z) (smallY A.small z)
          (freeTable A.small A.T A.b f) t) := by
  have heq := Fintype.sum_equiv (assignmentSplit A.small A.T A.hTG A.d A.b)
    (fun a => F (physicalProfile (fun a : I×J => A.small a.1 a.2)
      (fun a => width A.T A.d A.b a.1 a.2) z a))
    (fun a => F (profile A.small A.T A.d A.b (smallX A.small z) (smallY A.small z)
      (freeTable A.small A.T A.b a.2) a.1)) (by
      intro a
      apply congrArg F
      have he := split_profile A.small A.T A.hTG A.d A.b z
        ((assignmentSplit A.small A.T A.hTG A.d A.b) a)
      simpa only [Equiv.symm_apply_apply] using he)
  rw [heq,Fintype.sum_prod_type,Finset.sum_comm]

theorem h_eq_largeMarginal (A : Instance I J) (S : Selection A.T) (alpha : ℝ)
    {n : ℕ} (e : Fin n ≃ LargeCell (fun a : I×J => A.small a.1 a.2))
    (z : View A → ℕ) (hz : InBox (bounds A) z) :
    h A S alpha z=RootedLargeMarginal.largeMarginal A S alpha e z := by
  unfold RootedLargeMarginal.largeMarginal RootedPenalty.widths
  rw [sum_joined_eq_physical (fun a : I×J => A.small a.1 a.2)
    (fun a : I×J => width A.T A.d A.b a.1 a.2) e z (physicalWeight A S alpha)]
  trans (∑ f : FreeIndex A.small A.T A.b,∑ t : TreeIndex A.T A.d A.b,
    physicalWeight A S alpha (profile A.small A.T A.d A.b
      (smallX A.small z) (smallY A.small z) (freeTable A.small A.T A.b f) t))
  · unfold h
    apply Finset.sum_congr rfl
    intro f _
    apply (RootedLiteralCount.literal_tree_sum A S _ _ _ alpha ?_ ?_ ?_).symm
    · intro i j hs
      simpa only [smallX,hs,dite_eq_left,bounds] using hz (⟨(i,j),hs⟩,false)
    · intro i j hs
      simpa only [smallY,hs,dite_eq_left,bounds] using hz (⟨(i,j),hs⟩,true)
    · exact freeTable_bound A.small A.T A.b f
  · convert (physical_sum_split A z (physicalWeight A S alpha)).symm using 1
    all_goals
      congr 1
      ext
      simp

theorem h_removal (A : Instance I J) (S : Selection A.T)
    (alpha : ℝ) (ha : 0≤ alpha) (R : ℕ) :
    RemovalSlice (h A S alpha) (bounds A) R := by
  let e := (Fintype.equivFin (LargeCell (fun a : I×J => A.small a.1 a.2))).symm
  have hs := RootedLargeMarginal.largeMarginal_removal A S alpha ha e R
  intro z hz ht
  rw [NestedReindex.removal_congr_box _ _ (bounds A) z hz (h_eq_largeMarginal A S alpha e)]
  convert hs z hz ht using 1

theorem h_reflected (A : Instance I J) (S : Selection A.T)
    (alpha : ℝ) (ha : 0≤ alpha) (R : ℕ) :
    RemovalSlice (fun z => h A S alpha (IntegerReflection.reflect (bounds A) z)) (bounds A) R := by
  let e := (Fintype.equivFin (LargeCell (fun a : I×J => A.small a.1 a.2))).symm
  have hs := RootedLargeMarginal.largeMarginal_reflected A S alpha ha e R
  intro z hz ht
  rw [NestedReindex.removal_congr_box _ _ (bounds A) z hz (by
    intro x _
    apply h_eq_largeMarginal A S alpha e
    intro u
    exact Nat.sub_le _ _)]
  convert hs z hz ht using 1

end ContingencyTables.RootedCountIdentification

end OAI
