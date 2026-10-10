import OAI.Combinatorics.ContingencyTables.Rooted.RootedPenalty
import OAI.Combinatorics.ContingencyTables.Rooted.TreeMarginalEnumeration
import OAI.Combinatorics.ContingencyTables.Rooted.ForestBoxCardinality
import OAI.Combinatorics.ContingencyTables.Transport.PositiveSequenceInterpolation

namespace OAI

/-! # The actual one-tree physical marginal before the equality limit

One physical cell is retained as its doubled Boolean pair. Every other
physical cell, including small capacities zero and one, is summed at
balance. The resulting positive scalar sequence has the proved raw
log-concavity and finite interpolation bounds.
-/

namespace ContingencyTables.RootedTreeMarginal

open scoped BigOperators Classical Matrix Topology
open Filter CommonBasesFPRAS CompanionFactorialApplication ForestPenaltyApplication
open TreeMarginalSignature (keep singleView enumeration cellWidth otherWidths coordinateEquiv)
open LargePairEnumeration BalancedFamily BalancedBox EqualitySoftening IntegerWeightedTransport RowColumnPenalties

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def soft (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha L : ℝ) (t : I×J) : (Bool → ℕ) → ℝ :=
  eliminate (widths (otherWidths A t)) (fun z =>
    softenedWeight cellLine (RootedPenalty.rootFlag R) (fun _ => alpha)
      (lineOffset (ForestLiteralCount.lower A.T A.d A.b) (ForestLiteralCount.width A.T A.d A.b) A.r A.c)
      viewSlope (unaryRate A.T A.b alpha) (unaryEll (ForestLiteralCount.lower A.T A.d A.b))
      unarySlope (unaryCap A.b) L (z ∘ (coordinateEquiv A t).symm))

noncomputable def exactMarginal (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha : ℝ) (t : I×J) : (Bool → ℕ) → ℝ :=
  eliminate (widths (otherWidths A t)) (fun z =>
    RootedPenalty.physicalWeight A R alpha (z ∘ (coordinateEquiv A t).symm))

theorem soft_slices (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha L : ℝ) (t : I×J)
    (ha : 0 ≤ alpha) (hL : 0 ≤ L) :
    PositiveSlice (soft A R alpha L t) (fun _ => cellWidth A t) (cellWidth A t) ∧
      RemovalSlice (soft A R alpha L t) (fun _ => cellWidth A t) (cellWidth A t) := by
  apply EqualityReindex.physical_softened_slices_all
    (widths (otherWidths A t)) (fun _ => cellWidth A t) (cellWidth A t) (coordinateEquiv A t)
  · exact fun _ => ha
  · intro a
    unfold unaryRate
    split_ifs
    · exact div_nonneg ha (Nat.cast_nonneg _)
    · exact le_rfl
  · exact hL

noncomputable def scalarSoft (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha L : ℝ) (t : I×J) (k : ℕ) : ℝ :=
  soft A R alpha L t (childProfile (cellWidth A t) k)

noncomputable def scalarExact (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha : ℝ) (t : I×J) (k : ℕ) : ℝ :=
  exactMarginal A R alpha t (childProfile (cellWidth A t) k)

theorem scalar_positive (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha L : ℝ) (t : I×J)
    (ha : 0 ≤ alpha) (hL : 0 ≤ L) (k : ℕ) (hk : k ≤ cellWidth A t) :
    0 < scalarSoft A R alpha L t k :=
  (soft_slices A R alpha L t ha hL).1 _
    (childProfile_inBox _ _ hk) (childProfile_total _ _ hk)

theorem scalar_logConcave (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha L : ℝ) (t : I×J)
    (ha : 0 ≤ alpha) (hL : 0 ≤ L) (k : ℕ) (hk : k+2 ≤ cellWidth A t) :
    scalarSoft A R alpha L t k*scalarSoft A R alpha L t (k+2) ≤
      (scalarSoft A R alpha L t (k+1))^2 :=
  child_logConcave (soft A R alpha L t) _ (soft_slices A R alpha L t ha hL).1
    (soft_slices A R alpha L t ha hL).2 k hk

/-- Every retained tree mass is the finite equality-softening limit of
its actual positive physical balanced sum. -/
theorem scalar_tendsto (A : Instance I J) (R : RootedCompletion.Selection A.T) (alpha : ℝ) (t : I×J) (k : ℕ) :
    Tendsto (fun L : ℝ => scalarSoft A R alpha L t k) atTop (nhds (scalarExact A R alpha t k)) := by
  apply eliminate_tendsto (widths (otherWidths A t))
  intro z
  exact softenedWeight_tendsto cellLine (RootedPenalty.rootFlag R) (fun _ => alpha)
    (lineOffset (ForestLiteralCount.lower A.T A.d A.b) (ForestLiteralCount.width A.T A.d A.b) A.r A.c)
    viewSlope (unaryRate A.T A.b alpha) (unaryEll (ForestLiteralCount.lower A.T A.d A.b))
    unarySlope (unaryCap A.b) (z ∘ (coordinateEquiv A t).symm)

/-- The selected-root retained-cell marginal is the actual physical fibre. -/
theorem exact_eq_fibre (A : Instance I J) (R : RootedCompletion.Selection A.T)
    (alpha : ℝ) (t : I×J) (k : Fin (cellWidth A t+1)) :
    scalarExact A R alpha t k.val=
      BalancedCellFibres.fibre (cellWidth A) (RootedPenalty.physicalWeight A R alpha) t k := by
  unfold scalarExact exactMarginal
  rw [TreeMarginalSignature.eliminate_eq_one_cell_sum,BalancedCellFibres.fibre_eq_sum]
  apply Fintype.sum_equiv
    (Equiv.piCongrLeft (fun c : {c : I×J // c≠t} => Fin (cellWidth A c.val+1))
      (TreeMarginalSignature.otherCells t))
  intro a
  congr 1
  have h := TreeMarginalSignature.physical_one_cell_profile A t k
    ((Equiv.piCongrLeft (fun c : {c : I×J // c≠t} => Fin (cellWidth A c.val+1))
      (TreeMarginalSignature.otherCells t)) a)
  simpa only [Equiv.symm_apply_apply] using h

end ContingencyTables.RootedTreeMarginal

end OAI
