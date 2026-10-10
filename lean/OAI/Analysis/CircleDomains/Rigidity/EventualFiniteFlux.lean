import OAI.Analysis.CircleDomains.Topology.FiniteJordanModelInput
import OAI.Analysis.CircleDomains.Rigidity.ConditionalFiniteFlux
import OAI.Analysis.CircleDomains.Sobolev.ActualLocalIntegrability

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

 theorem MatchedRoundDisks.eventually_finite_flux_of_published_inputs (E : D.MatchedRoundDisks)
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
    (hrem : IsConformallyRemovable (frontier G)) :
    ∃ R₀ > 0, ∀ R ≥ R₀, ∀ F : Finset D.IndexedMatchedPair,
      quadrantFlux (D.selectedPlane hG.1 hf) 0 R ≤
        2*(∫ z in {z : ℂ | (z : Sphere) ∈ G} ∩ Metric.ball 0 R,
          ‖deriv (fun z : ℂ => finiteCoord (f (z : Sphere))) z‖)+
        2*Real.pi*(∑ j ∈ F, E.sourceRadius j*E.targetRadius j)+
        16*∑' j : {j : D.IndexedMatchedPair // j ∉ F}, E.sourceRadius j*E.targetRadius j := by
  obtain ⟨R₀,hR₀,hcontain⟩ := D.exists_source_containment_radius E hG.1 hinf
  refine ⟨R₀,hR₀,?_⟩
  intro R hR F
  exact E.finite_flux_of_published_inputs hmax hsolver hprincipal hsob hcross hplane hcoarea hLusin
    hsard hsch hsep hcollar hselect hgreen harea hcompact hfinite hmontel hhurwitz hzero
    harcs hstandard hpath hdual hlift hG hinf hf hfix hH hinf' hrem
    (hR₀.trans_le hR) (show R < R+1 by linarith)
    (D.actual_local_derivative_integrable hG.1 hinf hf hfix (R+1))
    (fun j => (hcontain j).trans (Metric.ball_subset_ball hR)) F

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
