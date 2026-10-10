import OAI.Analysis.CircleDomains.Topology.FiniteJordanModelInput
import OAI.Analysis.CircleDomains.Rigidity.NormalizedRigidityFromTrace
import OAI.Analysis.CircleDomains.Rigidity.AxialCommonPointTrace

namespace OAI

/-! Principal normalized rigidity from exactly the recorded published inputs. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 theorem normalized_identity_of_published_inputs
    (hmax : PlanarMaximalL2)
    (hsolver : PrincipalConductivityScalarSolver) (hprincipal : PrincipalRealBeltrami)
    (hsob : PlanarSobolevCoarea)
    (hcross : UnitDiskAlternatingContinua)
    (hplane : PlanarLipschitzFiberCoarea)
    (hcoarea : WeightedPlanarScalarCoarea) (hLusin : FiniteTorusAnalyticMeasurability)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (hcollar : SmoothRegularJordanCollars) (hselect : BorelPathRelationSelection)
    (hgreen : UnorientedFiniteCircleGreenFormula) (harea : ExteriorCoefficientAreaTheorem)
    (hcompact : SmoothCompactMetricSphereUniformization) (hfinite : FiniteJordanModelUniformization)
    (hmontel : MontelExhaustion) (hhurwitz : HurwitzUnivalentLimit) (hzero : HurwitzZeroFreeLimit)
    (harcs : ∀ C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    (hstandard : ∀ e : PathCodeData Sphere Sphere, [StandardBorelSpace (BasePathCode e)] →
      StandardBorelProbabilityLaws (BasePathCode e))
    (hpath : PolishProbabilityLaws C(PathTime, Sphere))
    (hdual : ∀ (e : PathCodeData Sphere Sphere)
      (I : Set ℕ) [PolishSpace I] (b : I → Sphere) (c : I → ℝ≥0∞)
      (ν : Measure Sphere) [IsFiniteMeasure ν]
      [StandardBorelSpace (ConstrainedCostCode e b c ν)],
      MeasureImageDuality (ConstrainedCostCode e b c ν) (PathCostSpace Sphere I))
    (hlift : ∀ (e : PathCodeData Sphere Sphere)
      (I : Set ℕ) [PolishSpace I] (b : I → Sphere) (c : I → ℝ≥0∞)
      (ν : Measure Sphere) [IsFiniteMeasure ν]
      [StandardBorelSpace (ConstrainedCostCode e b c ν)],
      MeasurePlanLifting (ConstrainedCostCode e b c ν) (PathCostSpace Sphere I))
    (hareaBound : ExteriorOmittedAreaTheorem)
    {G : Set Sphere} {f : Sphere → Sphere}
    (hG : IsCircleDomain G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G)) (hnorm : IsPrincipalNormalized f)
    (hH : IsCircleDomain (f '' G)) (hrem : IsConformallyRemovable (frontier G)) :
    ∀ p ∈ G, f p = p := by
  classical
  obtain ⟨D⟩ := exists_matched_conformal_ends hsard hsch hG.1 hG.2.1 hinf hf hnorm.1
  let : Countable D.IndexedMatchedPair := D.indexedMatchedPair_countable hG.1 hf
  let : Encodable D.IndexedMatchedPair := Encodable.ofCountable _
  have hinf' : OnePoint.infty ∈ f '' G := hnorm.1 ▸ mem_image_of_mem f hinf
  obtain ⟨E⟩ := D.exists_matched_round_disks hG hinf hf hH hinf'
  have ht := E.axial_commonPoint_trace_null_of_published_inputs hmax hsolver hprincipal hsob hcross
    hplane hcoarea hLusin hsard hsch hsep hcollar hselect hgreen harea hcompact hfinite
    hmontel hhurwitz hzero harcs hstandard hpath hdual hlift hG hinf hf hnorm.1 hH hinf' hrem
  exact D.normalized_identity_of_trace hareaBound E hG hinf hf hnorm hH (fun i => ht i i)

end CircleDomainRigidity

end

end OAI
