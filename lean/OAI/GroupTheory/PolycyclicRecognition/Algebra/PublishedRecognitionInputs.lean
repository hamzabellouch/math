import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanHeightPublishedAssembly
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CanonicalHeightContractionModel
import OAI.GroupTheory.PolycyclicRecognition.Geometry.RecognitionFromUniformHeight
import OAI.GroupTheory.PolycyclicRecognition.Geometry.LieModularInput
import OAI.GroupTheory.PolycyclicRecognition.Geometry.RepresentationFromDifferential
import OAI.GroupTheory.PolycyclicRecognition.Geometry.LieIntegrationNaturality
import OAI.GroupTheory.PolycyclicRecognition.Analysis.TraceFromKernelHaar
import OAI.GroupTheory.PolycyclicRecognition.Analysis.RemezFromInterpolation
import OAI.GroupTheory.PolycyclicRecognition.Geometry.MatrixDifferentialFromSmoothness
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolycyclicTorsionFree
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ConstructRiemannianInput
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ConstructChainMetric
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentModelIntegration
import OAI.GroupTheory.PolycyclicRecognition.Geometry.TriangularRealizationConstruction
import OAI.GroupTheory.PolycyclicRecognition.Algebra.DixmierRegularityFromTopology
import OAI.GroupTheory.PolycyclicRecognition.Geometry.IntrinsicTriangularRealization
import OAI.GroupTheory.PolycyclicRecognition.Lattices.SolvableLatticePolycyclic
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.CoarseFiniteness
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.SolvablePoincareFiniteness
import OAI.GroupTheory.PolycyclicRecognition.Analysis.NormalizedPairErgodicDecomposition
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CornulierTesseraConstruction
import OAI.GroupTheory.PolycyclicRecognition.Lattices.PolycyclicLatticeRealization

namespace OAI

/-! # Explicit published hypotheses for the recognition theorem

The hypotheses are elementary-amenable finiteness and polynomial-growth
recognition. The geometric height bounds, unimodularity, reduced cohomology,
and lattice realization are established independently.
-/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory
open scoped Manifold NNReal

attribute [local instance] stationaryL2Action zeroMeanL2Action

/-- The cited theorem families, specialized by the proof to its chosen
models. Gromov is retained solely as the polynomial-growth theorem. -/
structure PublishedRecognitionInputs : Prop where
  elementaryAmenableFiniteness : ElementaryAmenableFinitenessInput
  gromov : ∀ (K : Type) [Group K] [DecidableEq K], GromovPolynomialGrowthInput K

/-- Nilpotent kernel completion and the invariant graph prove the required
connected solvable lattice realization, including nonsplit extensions. -/
theorem PublishedRecognitionInputs.dekimpe (_h : PublishedRecognitionInputs) :
    DekimpeLatticeRealizationInput := dekimpeLatticeRealizationInput


/-- The compact rotational modification and its analytic triangular realization
supply all three proper cocompact comparison arrows. -/
theorem PublishedRecognitionInputs.triangulable (_h : PublishedRecognitionInputs) :
    CornulierTesseraModelInput := cornulierTesseraModelInput

/-- Controlled cycle fillings and finite projective covers prove FP transfer. -/
theorem PublishedRecognitionInputs.liFiniteness (_h : PublishedRecognitionInputs) :
    LiFinitenessInput := liFinitenessInput

/-- Controlled cochains and finite-resolution truncation prove duality transfer. -/
theorem PublishedRecognitionInputs.liDuality (_h : PublishedRecognitionInputs) :
    LiDualityInput := liDualityInput

/-- Rational top classes and integral finiteness prove the solvable PD endgame. -/
theorem PublishedRecognitionInputs.bieriDuality (_h : PublishedRecognitionInputs) :
    BieriDualityInput := bieriDualityInput

/-- The required solvable-lattice polycyclicity is proved using lifted complex
adjoint weights and the discrete nilpotent kernel, including rotational factors. -/
theorem PublishedRecognitionInputs.farbWeinberger (_h : PublishedRecognitionInputs) :
    FarbWeinbergerLatticeInput := isPolycyclic_uniformLattice_solvableLieGroup

/-- The finite BCH, nilpotent model, integration and Haar inputs are proved. -/
theorem PublishedRecognitionInputs.nilpotent (_h : PublishedRecognitionInputs) :
    NilpotentPublishedInputs := nilpotentPublishedInputs

/-- Interpolation and slicing give the fixed-power polynomial estimate. -/
theorem PublishedRecognitionInputs.remez (_h : PublishedRecognitionInputs) :
    RemezPolynomialInput := remezPolynomialInput

/-- The actual matrix Lie derivative is constructed from continuity. -/
theorem PublishedRecognitionInputs.differential (_h : PublishedRecognitionInputs) :
    MatrixLieDifferentialInput := matrixLieDifferentialInput

/-- Cyclic-series induction proves the finite-index torsion-free comparison. -/
theorem PublishedRecognitionInputs.torsionFree (_h : PublishedRecognitionInputs) :
    PolycyclicTorsionFreeIndexInput := polycyclicTorsionFreeIndexInput

/-- Compatible proper chain metrics are constructed from compact generation. -/
theorem PublishedRecognitionInputs.metric (_h : PublishedRecognitionInputs) :
    GeodesicMetricExistenceInput := geodesicMetricExistenceInput

/-- The invariant Riemannian metric, minimizing paths and coordinate bounds are constructed. -/
theorem PublishedRecognitionInputs.riemannian (_h : PublishedRecognitionInputs) :
    LieRiemannianMetricInput := lieRiemannianMetricInput

/-- The intrinsic height kernel gives the inducing triangular realization
without an exponential-chart hypothesis. -/
theorem PublishedRecognitionInputs.linearRealization (_h : PublishedRecognitionInputs)
    (R : SimplyConnectedSolvableLieModel) (d : ProperChainMetric R.carrier) :
    letI := d.compatibleMetric
    ExponentialLinearRealizationInput (EG := R.modelSpace) (G := R.carrier) := by
  let := d.compatibleMetric
  exact exponentialLinearRealizationInput_intrinsic

end PolycyclicRecognition

end

end OAI
