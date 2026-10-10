import OAI.Analysis.KadisonKastler.RandomWalkShiftLaw
import OAI.Analysis.KadisonKastler.ShiftInvariantFunctions

namespace OAI

/-! # The boundary as the invariant measurable space

Only its measurable structure enters the application. Keeping the original
points and restricting their sigma algebra gives the probability boundary
directly, with a nonsingular action induced by the rooted path action.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) (S : X → X)

def ShiftBoundarySpace (_μ : Measure X) (_S : X → X) := X

instance : MeasurableSpace (ShiftBoundarySpace μ S) :=
  @shiftInvariantSigma X ‹MeasurableSpace X› μ S

def shiftBoundaryMeasure : Measure (ShiftBoundarySpace μ S) := shiftInvariantMeasure μ S

instance [IsProbabilityMeasure μ] : IsProbabilityMeasure (shiftBoundaryMeasure μ S) :=
  shiftInvariantMeasure_probability μ S

def shiftBoundaryMap : X → ShiftBoundarySpace μ S := id

theorem shiftBoundaryMap_measurePreserving :
    MeasurePreserving (shiftBoundaryMap μ S) μ (shiftBoundaryMeasure μ S) := by
  refine ⟨measurable_id'' (shiftInvariantSigma_le μ S), ?_⟩
  exact (trim_eq_map (shiftInvariantSigma_le μ S)).symm

variable {G : Type*} [Group G]

def shiftBoundaryAction (α : NonsingularAction G X μ)
    (hc : ∀ g x, S (α.toPerm g x) = α.toPerm g (S x)) :
    NonsingularAction G (ShiftBoundarySpace μ S) (shiftBoundaryMeasure μ S) where
  toPerm := α.toPerm
  quasi g := quasi_shiftInvariantSigma_of_commuting μ S (α.toPerm g) (α.quasi g) (hc g)

@[simp]
theorem shiftBoundaryAction_apply (α : NonsingularAction G X μ)
    (hc : ∀ g x, S (α.toPerm g x) = α.toPerm g (S x)) (g : G) (x : X) :
    (shiftBoundaryAction μ S α hc).toPerm g (shiftBoundaryMap μ S x) =
      shiftBoundaryMap μ S (α.toPerm g x) := rfl

variable (G : Type*) [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]

abbrev RandomWalkBoundary :=
  ShiftBoundarySpace (randomWalkPathLaw G) (randomWalkAdvance G)

def randomWalkBoundaryMeasure : Measure (RandomWalkBoundary G) :=
  shiftBoundaryMeasure (randomWalkPathLaw G) (randomWalkAdvance G)

instance : IsProbabilityMeasure (randomWalkBoundaryMeasure G) :=
  inferInstanceAs (IsProbabilityMeasure
    (shiftBoundaryMeasure (randomWalkPathLaw G) (randomWalkAdvance G)))

def randomWalkBoundaryAction :
    NonsingularAction G (RandomWalkBoundary G) (randomWalkBoundaryMeasure G) :=
  shiftBoundaryAction (randomWalkPathLaw G) (randomWalkAdvance G)
    (randomWalkPathAction G) (randomWalkAdvance_action G)

end

end KadisonKastler

end OAI
