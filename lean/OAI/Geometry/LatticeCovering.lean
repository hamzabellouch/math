import OAI.Geometry.LatticeCovering.Model
import OAI.Geometry.LatticeCovering.Folded
import OAI.Geometry.LatticeCovering.Concentration
import OAI.Geometry.LatticeCovering.Rounding
import OAI.Geometry.LatticeCovering.Sampling
import OAI.Geometry.LatticeCovering.SamplingBounds
import OAI.Geometry.LatticeCovering.Bits
import OAI.Geometry.LatticeCovering.Lines
import OAI.Geometry.LatticeCovering.Chains
import OAI.Geometry.LatticeCovering.Products
import OAI.Geometry.LatticeCovering.Residuals
import OAI.Geometry.LatticeCovering.Patterns
import OAI.Geometry.LatticeCovering.Shears
import OAI.Geometry.LatticeCovering.Completion
import OAI.Geometry.LatticeCovering.Covering
import OAI.Geometry.LatticeCovering.Sections
import OAI.Geometry.LatticeCovering.Rates
import OAI.Geometry.LatticeCovering.Horizontal
import OAI.Geometry.LatticeCovering.Isotropy
import OAI.Geometry.LatticeCovering.GaussianSections
import OAI.Geometry.LatticeCovering.GridCounts
import OAI.Geometry.LatticeCovering.Transport
import OAI.Geometry.LatticeCovering.CircuitVolumes
import OAI.Geometry.LatticeCovering.CircuitLattices
import OAI.Geometry.LatticeCovering.CircuitSums
import OAI.Geometry.LatticeCovering.BrokenCircuits
import OAI.Geometry.LatticeCovering.PrimeGrids
import OAI.Geometry.LatticeCovering.CircuitErrors
import OAI.Geometry.LatticeCovering.PrimeKernels
import OAI.Geometry.LatticeCovering.MeanHoles
import OAI.Geometry.LatticeCovering.GaussianMoments
import OAI.Geometry.LatticeCovering.GaussianSmoothing
import OAI.Geometry.LatticeCovering.LogConcavity
import OAI.Geometry.LatticeCovering.RadialBounds
import OAI.Geometry.LatticeCovering.Marginals
import OAI.Geometry.LatticeCovering.ProjectionBounds
import OAI.Geometry.LatticeCovering.Desmoothing
import OAI.Geometry.LatticeCovering.GaussianRates
import OAI.Geometry.LatticeCovering.GaussianPositions
import OAI.Geometry.LatticeCovering.Assembly
import OAI.Geometry.LatticeCovering.Main

/-! Single-lattice coverings: the unconditional theorem and the full collection of
weighted Gaussian, sampling, shear, circuit, analytic, and geometric results.
Conditional interfaces keep their explicit hypotheses; the final theorem is unconditional. -/
