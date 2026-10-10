import OAI.Computability.PerfectCompleteness.Construction.StoppedProjectedBucketIndex
import OAI.Computability.PerfectCompleteness.Foundations.ProjectedWholeCut
import OAI.Computability.PerfectCompleteness.Foundations.SourceProjectedChoices

namespace OAI

section

namespace PerfectCompleteness.SourceProjectedWholeChoices

noncomputable section

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape
open UniqueGamesTheorem.Foundations.Games

variable {branch : Nat → Nat} {n i j t v m : Nat}

abbrev choiceLaw (child : Fin (branch i)) :
    FiniteDistribution (SourceProjectedChoices.Positions (branch := branch) (n := i) (t := t)) :=
  SourceProjectedChoices.choiceLaw child

variable (clauses : Fin m → SourceClause.NormalizedClause v)
  (rows : Nat → Nat) (hupper : j + 1 ≤ n) (hij : i < j)
  (designated : Fin (branch i) → Slots branch i)
  (hrows : ∀ k, 0 < rows (k + 1))
  (o : StoppedProjectedExperiment.Outer
    (branch := branch) (n := n) (j := j) (t := t) (m := m))
  (lowerPref : GeometricCutSplit.Prefix branch (j + 1) (i + 1))

abbrev path :=
  (StoppedProjectedExperiment.upperPath hupper o).append
    (GeometricCutSplit.prefixPath (Nat.succ_le_succ hij.le) lowerPref)

abbrev nativeCutSlots :=
  cutSlots (path hupper hij o lowerPref) (StoppedProjectedExperiment.nativeSlots clauses o)

abbrev projected :=
  SourceProjectedChoices.projected (nativeCutSlots clauses hupper hij o lowerPref)

abbrev projection :=
  SourceProjectedChoices.projection (nativeCutSlots clauses hupper hij o lowerPref)

private theorem filled_projection_heq (p : Path branch n (i + 1))
    (outside : Slots branch n → Fin t → MixedSupport.Slot)
    (left right₁ right₂ : Slots branch (i + 1) → Fin t → MixedSupport.Slot)
    (hleft : CutSlotAssembly.fill p outside left = outside) (hr : right₁ = right₂)
    (q₁ : ∀ leaf a, MixedSupport.Projection (left leaf a) (right₁ leaf a))
    (q₂ : ∀ leaf a, MixedSupport.Projection (left leaf a) (right₂ leaf a))
    (hq : HEq q₁ q₂) :
    HEq (fun leaf a => CutProjectionAssembly.castProjection
        (congrFun (congrFun hleft leaf) a) rfl
        (CutProjectionAssembly.fillProjection p outside left right₁ q₁ leaf a))
      (fun leaf a => CutProjectionAssembly.castProjection
        (congrFun (congrFun hleft leaf) a) rfl
        (CutProjectionAssembly.fillProjection p outside left right₂ q₂ leaf a)) := by
  subst right₂
  have hq' : q₁ = q₂ := eq_of_heq hq
  subst q₂
  rfl

theorem fullSlots_eq
    (choices : SourceProjectedChoices.Choices (branch := branch) (n := i) (t := t)) :
    ProjectedWholeCut.fullSlots (path hupper hij o lowerPref)
        (StoppedProjectedExperiment.nativeSlots clauses o)
        (projected clauses hupper hij o lowerPref) choices =
      StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated o
        (StoppedProjectedBucketIndex.key rows hrows
          (lowerPref, SourceProjectedChoices.tagEquiv choices)) := by
  have hinside := SourceProjectedChoices.selectedSlots_source clauses designated
    (StoppedProjectedExperiment.cutQuestions rows hupper hij o
      (StoppedProjectedBucketIndex.key rows hrows
        (lowerPref, SourceProjectedChoices.tagEquiv choices)))
    (SourceProjectedChoices.tagEquiv choices)
  simp only [Equiv.symm_apply_apply] at hinside
  exact congrArg (CutSlotAssembly.fill (path hupper hij o lowerPref)
    (StoppedProjectedExperiment.nativeSlots clauses o)) hinside

theorem fullProjection_heq
    (choices : SourceProjectedChoices.Choices (branch := branch) (n := i) (t := t)) :
    HEq (ProjectedWholeCut.fullProjection (path hupper hij o lowerPref)
        (StoppedProjectedExperiment.nativeSlots clauses o)
        (projected clauses hupper hij o lowerPref)
        (projection clauses hupper hij o lowerPref) choices)
      (StoppedProjectedExperiment.projection clauses rows hupper hij designated o
        (StoppedProjectedBucketIndex.key rows hrows
          (lowerPref, SourceProjectedChoices.tagEquiv choices))) := by
  have hinside := SourceProjectedChoices.selectedSlots_source clauses designated
    (StoppedProjectedExperiment.cutQuestions rows hupper hij o
      (StoppedProjectedBucketIndex.key rows hrows
        (lowerPref, SourceProjectedChoices.tagEquiv choices)))
    (SourceProjectedChoices.tagEquiv choices)
  have hprojection := SourceProjectedChoices.selectedProjection_source clauses designated
    (StoppedProjectedExperiment.cutQuestions rows hupper hij o
      (StoppedProjectedBucketIndex.key rows hrows
        (lowerPref, SourceProjectedChoices.tagEquiv choices)))
    (SourceProjectedChoices.tagEquiv choices)
  simp only [Equiv.symm_apply_apply] at hinside hprojection
  exact filled_projection_heq (path hupper hij o lowerPref)
    (StoppedProjectedExperiment.nativeSlots clauses o)
    (nativeCutSlots clauses hupper hij o lowerPref) _ _
    (ProjectedWholeCut.fill_native (path hupper hij o lowerPref)
      (StoppedProjectedExperiment.nativeSlots clauses o))
    hinside _ _ hprojection

end
end PerfectCompleteness.SourceProjectedWholeChoices

end

end OAI
