import OAI.Analysis.KadisonKastler.PublishedBoundary
import OAI.Analysis.KadisonKastler.RootBoundaryMeanConstruction
import OAI.Analysis.KadisonKastler.ProductBoundaryMeanConstruction
import OAI.Analysis.KadisonKastler.RandomWalkDoubleErgodicity

namespace OAI

/-! # Boundary means and double ergodicity

The fully supported symmetric random-walk law supplies scalar means
and unitary double ergodicity.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory

universe u

theorem publishedBoundary : PublishedBoundary.{u} := by
  intro G _ _ _ _
  let : MeasurableSpace G := ⊤
  let : MeasurableSingletonClass G := ⟨fun _ => trivial⟩
  exact ⟨RandomWalkBoundary G, inferInstance, randomWalkBoundaryMeasure G, inferInstance,
    randomWalkBoundaryAction G, ⟨randomWalkScalarBoundaryMean G⟩,
    ⟨randomWalkProductScalarMean G⟩, randomWalkUnitaryDoubleErgodic G⟩

end

end KadisonKastler

end OAI
