import OAI.Geometry.CylinderCovering.Angular.Admissibility
import OAI.Geometry.CylinderCovering.Angular.Aperture
import OAI.Geometry.CylinderCovering.Angular.Cubic
import OAI.Geometry.CylinderCovering.Angular.CubicEstimates
import OAI.Geometry.CylinderCovering.Angular.EqualPartition
import OAI.Geometry.CylinderCovering.Angular.GeneralArea
import OAI.Geometry.CylinderCovering.Angular.GeneralCap
import OAI.Geometry.CylinderCovering.Beams.FullStatement
import OAI.Geometry.CylinderCovering.Beams.PositivePart
import OAI.Geometry.CylinderCovering.Beams.RectangleCylinder
import OAI.Geometry.CylinderCovering.Caps.CoverageBounds
import OAI.Geometry.CylinderCovering.Caps.FiniteCylinders
import OAI.Geometry.CylinderCovering.Convexity.CanonicalRegularSimilarity
import OAI.Geometry.CylinderCovering.Convexity.CompactParallelogramCover
import OAI.Geometry.CylinderCovering.Convexity.ConvexPerturbationInverse
import OAI.Geometry.CylinderCovering.Convexity.FiniteCauchyVariation
import OAI.Geometry.CylinderCovering.Convexity.FinitePlaneMeasure
import OAI.Geometry.CylinderCovering.Convexity.GeneralCapFamily
import OAI.Geometry.CylinderCovering.Convexity.GeneralCapScalarHelpers
import OAI.Geometry.CylinderCovering.Convexity.InverseSqrtBounds
import OAI.Geometry.CylinderCovering.Convexity.OpenThickening
import OAI.Geometry.CylinderCovering.Convexity.RegularSimilarityBasis
import OAI.Geometry.CylinderCovering.Convexity.SpectralNormComparison
import OAI.Geometry.CylinderCovering.Convexity.ThresholdInverse
import OAI.Geometry.CylinderCovering.Cubic.ScalarEstimates
import OAI.Geometry.CylinderCovering.Footprints.Limits
import OAI.Geometry.CylinderCovering.Nilpotent.ExplicitCorollaries
import OAI.Geometry.CylinderCovering.Nilpotent.ZeroProfile
import OAI.Geometry.CylinderCovering.Physical.HalfTilt
import OAI.Geometry.CylinderCovering.Physical.MinimumExamples
import OAI.Geometry.CylinderCovering.Radial.Alignment
import OAI.Geometry.CylinderCovering.Rational.Bundle
import OAI.Geometry.CylinderCovering.Rational.NormalizedCost
import OAI.Geometry.CylinderCovering.Rational.PotentialExamples
import OAI.Geometry.CylinderCovering.Rational.StrictInverse
import OAI.Geometry.CylinderCovering.Rational.UncenteredCoefficients
import OAI.Geometry.CylinderCovering.Results
import OAI.Geometry.CylinderCovering.Simplex.ZeroShift

namespace OAI

namespace CylinderCovering

theorem fourPaperMain :
    AngularExplicitStatement ∧
    RuledApproximation.HyperbolicStatement ∧
    RuledApproximation.NilpotentC1Statement ∧
    RegularParallelogramCounterexampleStatement ∧
    RegularOpenCounterexampleStatement ∧
    RadialSweep.AlignedStatement ∧
    RadialSweep.ActualSweepStatement := by
  exact ⟨angularExplicit, ruledHistorical.1, nilpotentC1,
    regularParallelogramCounterexample, regularOpenCounterexample,
    radialAligned, radialActualSweep⟩

end CylinderCovering

end OAI
