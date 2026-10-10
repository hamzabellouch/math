import OAI.Combinatorics.ContingencyTables.Rooted.RootedPenalty
import OAI.Combinatorics.ContingencyTables.Rooted.ForestLargeMarginal

namespace OAI

/-! # Actual balanced large-cell marginal for the explicit root selector

The raw removal and reflected signatures are derived from the physical
line/unary factors. No signature of the marginal is postulated.
-/

namespace ContingencyTables.RootedLargeMarginal

open scoped BigOperators Classical
open CompanionFactorialApplication RootedCompletion RootedPenalty
open LargePairEnumeration BalancedBox

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def largeMarginal (A : Instance I J) (S : Selection A.T) (alpha : ℝ)
    {n : ℕ} (e : Fin n ≃ LargeCell (fun a : I×J => A.small a.1 a.2))
    (z : View A → ℕ) : ℝ :=
  ∑ a : ((k : Fin n) → Fin (RootedPenalty.widths A (e k).val.1 (e k).val.2+1)),
    physicalWeight A S alpha
      (joinedProfile (fun k => RootedPenalty.widths A (e k).val.1 (e k).val.2) z a ∘
        (physicalJoinEquiv (fun a : I×J => A.small a.1 a.2) e).symm)

theorem largeMarginal_nonnegative (A : Instance I J) (S : Selection A.T) (alpha : ℝ)
    {n : ℕ} (e : Fin n ≃ LargeCell (fun a : I×J => A.small a.1 a.2))
    (z : View A → ℕ) : 0≤ largeMarginal A S alpha e z := by
  apply Finset.sum_nonneg
  intro a _
  exact physicalWeight_nonnegative A S alpha _

private theorem largeMarginal_eq_eliminate (A : Instance I J) (S : Selection A.T)
    (alpha : ℝ) {n : ℕ} (e : Fin n ≃ LargeCell (fun a : I×J => A.small a.1 a.2)) :
    largeMarginal A S alpha e=
      BalancedFamily.eliminate (LargePairEnumeration.widths
        (fun k => RootedPenalty.widths A (e k).val.1 (e k).val.2)) (fun q =>
          physicalWeight A S alpha
            (q ∘ (physicalCoordinateEquiv (fun a : I×J => A.small a.1 a.2) e
              (fun k => RootedPenalty.widths A (e k).val.1 (e k).val.2)).symm)) := by
  funext z
  exact (eliminate_eq_actual_cells (fun a : I×J => A.small a.1 a.2) e _
    (physicalWeight A S alpha) z).symm

lemma large_width (A : Instance I J) {n : ℕ}
    (e : Fin n ≃ LargeCell (fun a : I×J => A.small a.1 a.2)) (k : Fin n) :
    2≤ RootedPenalty.widths A (e k).val.1 (e k).val.2 := by
  have hb := (A.hlarge _ _ (e k).property).2
  by_cases ht : A.T.Adj (.inl (e k).val.1) (.inr (e k).val.2)
  · simp only [RootedPenalty.widths,ForestLiteralCount.width,ht,ite_true]
    have hd := A.hd
    have hp : 0<A.d*A.b (e k).val.1 (e k).val.2 := Nat.mul_pos (by omega) (by omega)
    nlinarith
  · simp only [RootedPenalty.widths,ForestLiteralCount.width,ht,ite_false]
    exact A.hW.trans (A.hlarge _ _ (e k).property).1

theorem largeMarginal_removal (A : Instance I J) (S : Selection A.T)
    (alpha : ℝ) (ha : 0≤ alpha) {n : ℕ}
    (e : Fin n ≃ LargeCell (fun a : I×J => A.small a.1 a.2)) (R : ℕ) :
    RemovalSlice (largeMarginal A S alpha e) (bounds A) R := by
  let N : Fin n → ℕ := fun k => RootedPenalty.widths A (e k).val.1 (e k).val.2
  have hu : ∀ a,0≤ ForestPenaltyApplication.unaryRate A.T A.b alpha a := by
    intro a
    unfold ForestPenaltyApplication.unaryRate
    split_ifs
    · exact div_nonneg ha (Nat.cast_nonneg _)
    · exact le_rfl
  have hs := EqualityReindex.physical_marginal_removal (LargePairEnumeration.widths N)
    (bounds A) R (physicalCoordinateEquiv (fun a : I×J => A.small a.1 a.2) e N)
    RowColumnPenalties.cellLine (rootFlag S) (fun _ => alpha)
    (ForestPenaltyApplication.lineOffset (ell A) (RootedPenalty.widths A) A.r A.c)
    RowColumnPenalties.viewSlope (ForestPenaltyApplication.unaryRate A.T A.b alpha)
    (ForestPenaltyApplication.unaryEll (ell A)) ForestPenaltyApplication.unarySlope
    (ForestPenaltyApplication.unaryCap A.b)
    (widths_lower N (large_width A e)) (fun _ => ha) hu
  rw [largeMarginal_eq_eliminate]
  exact hs

theorem largeMarginal_reflected (A : Instance I J) (S : Selection A.T)
    (alpha : ℝ) (ha : 0≤ alpha) {n : ℕ}
    (e : Fin n ≃ LargeCell (fun a : I×J => A.small a.1 a.2)) (R : ℕ) :
    RemovalSlice (fun z => largeMarginal A S alpha e
      (IntegerReflection.reflect (bounds A) z)) (bounds A) R := by
  let N : Fin n → ℕ := fun k => RootedPenalty.widths A (e k).val.1 (e k).val.2
  have hu : ∀ a,0≤ ForestPenaltyApplication.unaryRate A.T A.b alpha a := by
    intro a
    unfold ForestPenaltyApplication.unaryRate
    split_ifs
    · exact div_nonneg ha (Nat.cast_nonneg _)
    · exact le_rfl
  rw [largeMarginal_eq_eliminate]
  exact EqualityReindex.physical_marginal_reflected (LargePairEnumeration.widths N)
    (bounds A) R (physicalCoordinateEquiv (fun a : I×J => A.small a.1 a.2) e N)
    RowColumnPenalties.cellLine (rootFlag S) (fun _ => alpha)
    (ForestPenaltyApplication.lineOffset (ell A) (RootedPenalty.widths A) A.r A.c)
    RowColumnPenalties.viewSlope (ForestPenaltyApplication.unaryRate A.T A.b alpha)
    (ForestPenaltyApplication.unaryEll (ell A)) ForestPenaltyApplication.unarySlope
    (ForestPenaltyApplication.unaryCap A.b)
    (widths_lower N (large_width A e)) (fun _ => ha) hu

end ContingencyTables.RootedLargeMarginal

end OAI
