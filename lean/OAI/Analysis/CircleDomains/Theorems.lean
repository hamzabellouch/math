import OAI.Analysis.CircleDomains.Topology.FiniteJordanModelInput
import OAI.Analysis.CircleDomains.Uniformization.ConstructedFiniteModels
import OAI.Analysis.CircleDomains.Rigidity.PrincipalScalarSolverProof
import OAI.Analysis.CircleDomains.Rigidity.PrincipalRealBeltramiProof
import OAI.Analysis.CircleDomains.Uniformization.SmoothMetricUniformizationProof
import OAI.Analysis.CircleDomains.Topology.PlanarSchoenfliesProof
import OAI.Analysis.CircleDomains.Probability.MeasureImageDualityProof
import OAI.Analysis.CircleDomains.Topology.FiniteCircleGreenProof
import OAI.Analysis.CircleDomains.Selection.ConditionalKoebe
import OAI.Analysis.CircleDomains.Rigidity.ConditionalRigidity
import OAI.Analysis.CircleDomains.Uniformization.HurwitzUnivalentProof
import OAI.Analysis.CircleDomains.Uniformization.MontelProof
import OAI.Analysis.CircleDomains.Probability.AnalyticFiniteMeasurability
import OAI.Analysis.CircleDomains.Topology.PathSelectionProof
import OAI.Analysis.CircleDomains.Sobolev.SardProof
import OAI.Analysis.CircleDomains.Probability.ProbabilityImageLifting
import OAI.Analysis.CircleDomains.Topology.PlanarMaximalProof
import OAI.Analysis.CircleDomains.Probability.StandardBorelProbabilityProof
import OAI.Analysis.CircleDomains.Probability.PolishProbabilityProof
import OAI.Analysis.CircleDomains.Sobolev.LipschitzCoareaProof
import OAI.Analysis.CircleDomains.Sobolev.WeightedPlanarCoareaProof
import OAI.Analysis.CircleDomains.Topology.SimpleArcsProof
import OAI.Analysis.CircleDomains.Sobolev.SobolevCoareaProof
import OAI.Analysis.CircleDomains.Sobolev.ExteriorCoefficientAreaProof
import OAI.Analysis.CircleDomains.Topology.RegularJordanCollarProof
import OAI.Analysis.CircleDomains.Topology.CrosscutSeparationProof
import OAI.Analysis.CircleDomains.Topology.DiskCrossingProof

namespace OAI

/-! Circle-domain uniformization from finite Jordan models constructed by invariant
Beltrami reflection, and rigidity under conformal removability. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

theorem koebeCircleDomainConjecture_of_finite_circle_uniformization
    (hfinite : FiniteCircleUniformization)
    : KoebeCircleDomainConjecture := by
  have hsch : PlanarSchoenflies := planarSchoenflies
  have hcompact : SmoothCompactMetricSphereUniformization := smoothCompactMetricSphereUniformization
  exact koebeCircleDomainConjecture_of_constructed_quotient (unitDiskAlternatingContinua hsch) planarLipschitzFiberCoarea weightedPlanarScalarCoarea finiteTorusAnalyticMeasurability
    smoothPlanarSard hsch (unitDiskCrosscutSeparation hsch) (smoothRegularJordanCollars unorientedFiniteCircleGreenFormula) borelPathRelationSelection unorientedFiniteCircleGreenFormula (exteriorCoefficientAreaTheorem hsch unorientedFiniteCircleGreenFormula) hcompact (finiteCircleUniformization_jordanModels hfinite) montelExhaustion
    hurwitzUnivalentLimit hurwitzZeroFreeLimit (by
      intro C hC hLC
      let : CompactSpace C := isCompact_iff_compactSpace.mp hC
      let : LocallyConnectedSpace C := hLC
      exact hasSimpleArcsInConnectedOpens_compact_metric C) (by intros; exact standardBorelProbabilityLaws _) (polishProbabilityLaws _) (by intros; exact measureImageDuality _ _) (by intros; exact measurePlanLifting _ _)


theorem koebeCircleDomainConjecture_of_remaining_published_inputs
    (_hmoore : MooreSphereDecomposition) (hfinite : FiniteCircleUniformization) :
    KoebeCircleDomainConjecture :=
  koebeCircleDomainConjecture_of_finite_circle_uniformization hfinite

theorem circleDomainRemovabilityRigidity_of_remaining_published_inputs
    (hfinite : FiniteCircleUniformization)
    : CircleDomainRemovabilityRigidity := by
  have hsch : PlanarSchoenflies := planarSchoenflies
  have hcompact : SmoothCompactMetricSphereUniformization := smoothCompactMetricSphereUniformization
  exact circleDomainRemovabilityRigidity_of_scalar_solver planarMaximalL2 principalConductivityScalarSolver principalRealBeltrami planarSobolevCoarea (unitDiskAlternatingContinua hsch)
    planarLipschitzFiberCoarea weightedPlanarScalarCoarea finiteTorusAnalyticMeasurability smoothPlanarSard hsch (unitDiskCrosscutSeparation hsch) (smoothRegularJordanCollars unorientedFiniteCircleGreenFormula) borelPathRelationSelection unorientedFiniteCircleGreenFormula (exteriorCoefficientAreaTheorem hsch unorientedFiniteCircleGreenFormula) hcompact (finiteCircleUniformization_jordanModels hfinite)
    montelExhaustion hurwitzUnivalentLimit hurwitzZeroFreeLimit (by
      intro C hC hLC
      let : CompactSpace C := isCompact_iff_compactSpace.mp hC
      let : LocallyConnectedSpace C := hLC
      exact hasSimpleArcsInConnectedOpens_compact_metric C) (by intros; exact standardBorelProbabilityLaws _) (polishProbabilityLaws _) (by intros; exact measureImageDuality _ _) (by intros; exact measurePlanLifting _ _) (exteriorOmittedAreaTheorem hsch unorientedFiniteCircleGreenFormula)

omit [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)] in
theorem koebeCircleDomainConjecture
    : KoebeCircleDomainConjecture := by
  let : MeasurableSpace C(PathTime, Sphere) := borel _
  let : BorelSpace C(PathTime, Sphere) := ⟨rfl⟩
  have hsch : PlanarSchoenflies := planarSchoenflies
  have hcompact : SmoothCompactMetricSphereUniformization := smoothCompactMetricSphereUniformization
  exact koebeCircleDomainConjecture_of_constructed_quotient (unitDiskAlternatingContinua hsch) planarLipschitzFiberCoarea weightedPlanarScalarCoarea finiteTorusAnalyticMeasurability
    smoothPlanarSard hsch (unitDiskCrosscutSeparation hsch) (smoothRegularJordanCollars unorientedFiniteCircleGreenFormula) borelPathRelationSelection unorientedFiniteCircleGreenFormula (exteriorCoefficientAreaTheorem hsch unorientedFiniteCircleGreenFormula) hcompact finiteJordanModelUniformization montelExhaustion
    hurwitzUnivalentLimit hurwitzZeroFreeLimit (by
      intro C hC hLC
      let : CompactSpace C := isCompact_iff_compactSpace.mp hC
      let : LocallyConnectedSpace C := hLC
      exact hasSimpleArcsInConnectedOpens_compact_metric C) (by intros; exact standardBorelProbabilityLaws _) (polishProbabilityLaws _) (by intros; exact measureImageDuality _ _) (by intros; exact measurePlanLifting _ _)


/- The full published finite-circle existence statement follows from
 the unconditional Koebe theorem; the proof above only used the constructed
 finite Jordan models. -/
omit [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)] in
theorem finiteCircleUniformization : FiniteCircleUniformization := by
  intro U hU hconn _ _
  exact koebeCircleDomainConjecture U hU hconn

omit [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)] in
theorem circleDomainRemovabilityRigidity : CircleDomainRemovabilityRigidity := by
  let : MeasurableSpace C(PathTime, Sphere) := borel _
  let : BorelSpace C(PathTime, Sphere) := ⟨rfl⟩
  exact circleDomainRemovabilityRigidity_of_remaining_published_inputs finiteCircleUniformization

end CircleDomainRigidity

end

end OAI
