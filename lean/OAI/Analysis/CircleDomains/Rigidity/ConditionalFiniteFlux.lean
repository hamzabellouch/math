import OAI.Analysis.CircleDomains.Topology.FiniteJordanModelInput
import OAI.Analysis.CircleDomains.Rigidity.ActualFiniteFluxLimit
import OAI.Analysis.CircleDomains.Rigidity.AxialCommonPointTrace

namespace OAI

/-! Finite-hole flux from axial slice estimates, multiplicity bounds,
circle integration, and shrinking-hole limits. The outer principal flux
is an explicit hypothesis. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} {D : MatchedConformalEnds G f}
variable [Encodable D.IndexedMatchedPair]

 theorem MatchedRoundDisks.finite_flux_of_published_inputs (E : D.MatchedRoundDisks)
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
    (hG : IsCircleDomain G) (hinf : OnePoint.infty ∈ G)
    (hf : IsConformalEquivalence f G (f '' G)) (hfix : f OnePoint.infty = OnePoint.infty)
    (hH : IsCircleDomain (f '' G)) (hinf' : OnePoint.infty ∈ f '' G)
    (hrem : IsConformallyRemovable (frontier G))
    {R W : ℝ} (hR : 0 < R) (hRW : R < W)
    (hρ : IntegrableOn (fun z => ‖deriv (fun z : ℂ => finiteCoord (f (z : Sphere))) z‖)
      ({z : ℂ | (z : Sphere) ∈ G} ∩ Metric.ball 0 W) volume)
    (hcontain : ∀ j, Metric.closedBall (E.sourceCenter j) (E.sourceRadius j) ⊆ Metric.ball 0 R)
    (F : Finset D.IndexedMatchedPair) :

    quadrantFlux (D.selectedPlane hG.1 hf) 0 R ≤
      2*(∫ z in {z : ℂ | (z : Sphere) ∈ G} ∩ Metric.ball 0 R,
        ‖deriv (fun z : ℂ => finiteCoord (f (z : Sphere))) z‖)+
      2*Real.pi*(∑ j ∈ F, E.sourceRadius j*E.targetRadius j)+
      16*∑' j : {j : D.IndexedMatchedPair // j ∉ F}, E.sourceRadius j*E.targetRadius j := by
  have ht := E.axial_commonPoint_trace_null_of_published_inputs hmax hsolver hprincipal hsob hcross
    hplane hcoarea hLusin hsard hsch hsep hcollar hselect hgreen harea hcompact hfinite
    hmontel hhurwitz hzero harcs hstandard hpath hdual hlift hG hinf hf hfix hH hinf' hrem
  exact D.actual_finite_flux_of_trace E hG hinf hf hfix hH hinf' hR hRW
    (fun i => ht i i) hρ hcontain F

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
