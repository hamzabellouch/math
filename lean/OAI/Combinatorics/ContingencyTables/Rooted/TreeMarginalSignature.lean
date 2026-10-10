import OAI.Combinatorics.ContingencyTables.Sampling.AllBalancedWidths
import OAI.Combinatorics.ContingencyTables.Rooted.ForestBoxCardinality
import OAI.Combinatorics.ContingencyTables.Transport.PositiveSequenceInterpolation

namespace OAI

/-! # The actual one-tree physical marginal before the equality limit

One physical cell is retained as its doubled Boolean pair. Every other
physical cell, including small capacities zero and one, is summed at
balance. The resulting positive scalar sequence has the proved raw
log-concavity and finite interpolation bounds.
-/

namespace ContingencyTables.TreeMarginalSignature

open scoped BigOperators Classical Matrix Topology
open Filter CommonBasesFPRAS CompanionFactorialApplication ForestPenaltyApplication
open LargePairEnumeration BalancedFamily BalancedBox EqualitySoftening IntegerWeightedTransport RowColumnPenalties

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def keep (t a : I×J) : Bool := decide (a=t)

noncomputable def singleView (t : I×J) : SmallView (keep t) ≃ Bool where
  toFun p := p.2
  invFun b := (⟨t,by simp [keep]⟩,b)
  left_inv p := by
    have hp : p.1.val=t := by simpa only [keep,decide_eq_true_eq] using p.1.property
    rcases p with ⟨⟨a,ha⟩,b⟩
    dsimp only at hp
    subst a
    rfl
  right_inv b := rfl

noncomputable def enumeration (t : I×J) : Fin (Fintype.card (LargeCell (keep t))) ≃ LargeCell (keep t) :=
  (Fintype.equivFin _).symm

noncomputable def cellWidth (A : Instance I J) (a : I×J) : ℕ :=
  ForestLiteralCount.width A.T A.d A.b a.1 a.2

noncomputable def otherWidths (A : Instance I J) (t : I×J) :
    Fin (Fintype.card (LargeCell (keep t))) → ℕ := fun k => cellWidth A (enumeration t k).val

noncomputable def coordinateEquiv (A : Instance I J) (t : I×J) :
    Coordinates Bool (widths (otherWidths A t)) ≃ (I×J)×Bool :=
  (LargePairEnumeration.coordinateEquiv Bool (otherWidths A t)).trans
    ((Equiv.sumCongr (singleView t).symm (Equiv.refl _)).trans
      (physicalJoinEquiv (keep t) (enumeration t)))

noncomputable def soft (A : Instance I J) (alpha L : ℝ) (t : I×J) : (Bool → ℕ) → ℝ :=
  eliminate (widths (otherWidths A t)) (fun z =>
    softenedWeight cellLine (rootFlag A.T) (fun _ => alpha)
      (lineOffset (ForestLiteralCount.lower A.T A.d A.b) (ForestLiteralCount.width A.T A.d A.b) A.r A.c)
      viewSlope (unaryRate A.T A.b alpha) (unaryEll (ForestLiteralCount.lower A.T A.d A.b))
      unarySlope (unaryCap A.b) L (z ∘ (coordinateEquiv A t).symm))

noncomputable def exactMarginal (A : Instance I J) (alpha : ℝ) (t : I×J) : (Bool → ℕ) → ℝ :=
  eliminate (widths (otherWidths A t)) (fun z =>
    physicalWeight A.T A.b (ForestLiteralCount.lower A.T A.d A.b)
      (ForestLiteralCount.width A.T A.d A.b) A.r A.c alpha (z ∘ (coordinateEquiv A t).symm))

theorem soft_slices (A : Instance I J) (alpha L : ℝ) (t : I×J)
    (ha : 0 ≤ alpha) (hL : 0 ≤ L) :
    PositiveSlice (soft A alpha L t) (fun _ => cellWidth A t) (cellWidth A t) ∧
      RemovalSlice (soft A alpha L t) (fun _ => cellWidth A t) (cellWidth A t) := by
  apply EqualityReindex.physical_softened_slices_all
    (widths (otherWidths A t)) (fun _ => cellWidth A t) (cellWidth A t) (coordinateEquiv A t)
  · exact fun _ => ha
  · intro a
    unfold unaryRate
    split_ifs
    · exact div_nonneg ha (Nat.cast_nonneg _)
    · exact le_rfl
  · exact hL

noncomputable def scalarSoft (A : Instance I J) (alpha L : ℝ) (t : I×J) (k : ℕ) : ℝ :=
  soft A alpha L t (childProfile (cellWidth A t) k)

noncomputable def scalarExact (A : Instance I J) (alpha : ℝ) (t : I×J) (k : ℕ) : ℝ :=
  exactMarginal A alpha t (childProfile (cellWidth A t) k)

theorem scalar_positive (A : Instance I J) (alpha L : ℝ) (t : I×J)
    (ha : 0 ≤ alpha) (hL : 0 ≤ L) (k : ℕ) (hk : k ≤ cellWidth A t) :
    0 < scalarSoft A alpha L t k :=
  (soft_slices A alpha L t ha hL).1 _
    (childProfile_inBox _ _ hk) (childProfile_total _ _ hk)

theorem scalar_logConcave (A : Instance I J) (alpha L : ℝ) (t : I×J)
    (ha : 0 ≤ alpha) (hL : 0 ≤ L) (k : ℕ) (hk : k+2 ≤ cellWidth A t) :
    scalarSoft A alpha L t k*scalarSoft A alpha L t (k+2) ≤
      (scalarSoft A alpha L t (k+1))^2 :=
  child_logConcave (soft A alpha L t) _ (soft_slices A alpha L t ha hL).1
    (soft_slices A alpha L t ha hL).2 k hk

/-- Every retained tree mass is the finite equality-softening limit of
its actual positive physical balanced sum. -/
theorem scalar_tendsto (A : Instance I J) (alpha : ℝ) (t : I×J) (k : ℕ) :
    Tendsto (fun L : ℝ => scalarSoft A alpha L t k) atTop (nhds (scalarExact A alpha t k)) := by
  apply eliminate_tendsto (widths (otherWidths A t))
  intro z
  exact softenedWeight_tendsto cellLine (rootFlag A.T) (fun _ => alpha)
    (lineOffset (ForestLiteralCount.lower A.T A.d A.b) (ForestLiteralCount.width A.T A.d A.b) A.r A.c)
    viewSlope (unaryRate A.T A.b alpha) (unaryEll (ForestLiteralCount.lower A.T A.d A.b))
    unarySlope (unaryCap A.b) (z ∘ (coordinateEquiv A t).symm)

end ContingencyTables.TreeMarginalSignature

end OAI
