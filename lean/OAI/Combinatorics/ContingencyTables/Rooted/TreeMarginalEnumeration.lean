import OAI.Combinatorics.ContingencyTables.Rooted.TreeMarginalSignature
import OAI.Combinatorics.ContingencyTables.Transport.BalancedCellFibres

namespace OAI

/-! # The physical one-cell marginal is exactly its balanced assignment fibre -/

namespace ContingencyTables.TreeMarginalSignature

open scoped BigOperators Classical
open CompanionFactorialApplication ForestPenaltyApplication LargePairEnumeration
open PhysicalLargeProfiles BalancedFamily BalancedEnumeration BalancedCellFibres
open IntegerWeightedTransport

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def otherCells (t : I×J) : LargeCell (keep t) ≃ {a : I×J // a≠t} where
  toFun a := ⟨a.val,by simpa only [keep,decide_eq_false_iff_not] using a.property⟩
  invFun a := ⟨a.val,by simpa only [keep,decide_eq_false_iff_not] using a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma one_view_reindex (A : Instance I J) (t : I×J) (z : Bool → ℕ)
    (a : (k : Fin (Fintype.card (LargeCell (keep t)))) → Fin (otherWidths A t k+1)) :
    joinedProfile (otherWidths A t) z a ∘
      ((Equiv.sumCongr (singleView t).symm (Equiv.refl _)).trans
        (physicalJoinEquiv (keep t) (enumeration t))).symm=
      joinedProfile (otherWidths A t) (z ∘ singleView t) a ∘
        (physicalJoinEquiv (keep t) (enumeration t)).symm := by
  funext u
  change joinedProfile (otherWidths A t) z a
    ((Equiv.sumCongr (singleView t).symm (Equiv.refl _)).symm
      ((physicalJoinEquiv (keep t) (enumeration t)).symm u))=
    joinedProfile (otherWidths A t) (z ∘ singleView t) a
      ((physicalJoinEquiv (keep t) (enumeration t)).symm u)
  generalize (physicalJoinEquiv (keep t) (enumeration t)).symm u=q
  cases q <;> rfl

lemma eliminate_eq_view_sum (A : Instance I J) (t : I×J)
    (F : ((I×J)×Bool → ℕ) → ℝ) (z : Bool → ℕ) :
    eliminate (widths (otherWidths A t)) (fun q => F (q ∘ (coordinateEquiv A t).symm)) z=
      ∑ a : ((k : Fin (Fintype.card (LargeCell (keep t)))) → Fin (otherWidths A t k+1)),
        F (joinedProfile (otherWidths A t) (z ∘ singleView t) a ∘
          (physicalJoinEquiv (keep t) (enumeration t)).symm) := by
  change eliminate (widths (otherWidths A t)) (fun q =>
    F ((q ∘ (LargePairEnumeration.coordinateEquiv Bool (otherWidths A t)).symm) ∘
      ((Equiv.sumCongr (singleView t).symm (Equiv.refl _)).trans
        (physicalJoinEquiv (keep t) (enumeration t))).symm)) z=_
  rw [LargePairEnumeration.eliminate_eq_physical_sum (otherWidths A t)
    (fun q => F (q ∘ ((Equiv.sumCongr (singleView t).symm (Equiv.refl _)).trans
      (physicalJoinEquiv (keep t) (enumeration t))).symm)) z]
  apply Finset.sum_congr rfl
  intro a _
  exact congrArg F (one_view_reindex A t z a)

theorem eliminate_eq_one_cell_sum (A : Instance I J) (t : I×J)
    (F : ((I×J)×Bool → ℕ) → ℝ) (z : Bool → ℕ) :
    eliminate (widths (otherWidths A t)) (fun q => F (q ∘ (coordinateEquiv A t).symm)) z=
      ∑ a : PhysicalAssignments (keep t) (cellWidth A),
        F (physicalProfile (keep t) (cellWidth A) (z ∘ singleView t) a) := by
  rw [eliminate_eq_view_sum]
  convert sum_joined_eq_physical (keep t) (cellWidth A) (enumeration t) (z ∘ singleView t) F using 1
  · rfl
  · apply Finset.sum_congr
    · ext a
      simp
    · intro a _
      rfl

lemma physical_one_cell_profile (A : Instance I J) (t : I×J)
    (k : Fin (cellWidth A t+1)) (a : BalancedCellFibres.Others (cellWidth A) t) :
    physicalProfile (keep t) (cellWidth A) (childProfile (cellWidth A t) k.val ∘ singleView t)
      ((Equiv.piCongrLeft (fun c : {c : I×J // c≠t} => Fin (cellWidth A c.val+1))
        (otherCells t)).symm a)=
      BalancedCellFibres.profile (cellWidth A) (join (cellWidth A) t k a) := by
  funext u
  rcases u with ⟨c,b⟩
  by_cases hc : c=t
  · subst c
    cases b <;> simp [physicalProfile,keep,singleView,BalancedCellFibres.profile,join_at] <;> rfl
  · have hkeep : keep t c=false := by simp only [keep,decide_eq_false_iff_not]; exact hc
    simp only [physicalProfile,hkeep,Bool.false_eq_true,dite_false,BalancedCellFibres.profile]
    rw [join_other (cellWidth A) t k a ⟨c,hc⟩]
    rfl

/-- No multiplicity or factorial appears: the exact retained-cell
balanced marginal is the literal full physical assignment fibre. -/
theorem exact_eq_fibre (A : Instance I J) (alpha : ℝ) (t : I×J)
    (k : Fin (cellWidth A t+1)) :
    scalarExact A alpha t k.val=
      fibre (cellWidth A)
        (physicalWeight A.T A.b (ForestLiteralCount.lower A.T A.d A.b)
          (ForestLiteralCount.width A.T A.d A.b) A.r A.c alpha) t k := by
  unfold scalarExact exactMarginal
  rw [eliminate_eq_one_cell_sum,fibre_eq_sum]
  apply Fintype.sum_equiv
    (Equiv.piCongrLeft (fun c : {c : I×J // c≠t} => Fin (cellWidth A c.val+1)) (otherCells t))
  intro a
  congr 1
  have h := physical_one_cell_profile A t k
    ((Equiv.piCongrLeft (fun c : {c : I×J // c≠t} => Fin (cellWidth A c.val+1)) (otherCells t)) a)
  simpa only [Equiv.symm_apply_apply] using h

end ContingencyTables.TreeMarginalSignature

end OAI
