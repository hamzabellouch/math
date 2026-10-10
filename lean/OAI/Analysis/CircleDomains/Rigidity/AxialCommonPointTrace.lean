import OAI.Analysis.CircleDomains.Topology.FiniteJordanModelInput
import OAI.Analysis.CircleDomains.Selection.SelectedCoordinateTest
import OAI.Analysis.CircleDomains.Rigidity.SmoothCommonPointTrace
import OAI.Analysis.CircleDomains.Rigidity.GlobalSmoothMatchedMasks
import OAI.Analysis.CircleDomains.Rigidity.MatchedRealMaskConstruction
import OAI.Analysis.CircleDomains.Rigidity.MatchedMaskGlobalSobolev

namespace OAI

/-! The exact four axial trace conclusions for the singleton-to-singleton
part of the matched correspondence, from the recorded published inputs. -/
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

 theorem MatchedRoundDisks.axial_commonPoint_trace_null_of_published_inputs (E : D.MatchedRoundDisks)
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
    ∀ i k : Fin 2, ∀ᵐ y ∂volume,
      volume ((fun x => (complexPlaneCoordinates.symm (finiteCoord
        (D.selectedTarget hG.1 hf (complexCoordinateLine i y x : Sphere)))) k) ''
        {x | complexCoordinateLine i y x ∈ D.commonPointPlane}) = 0 := by
  intro i k
  obtain ⟨Φ,hΦ,hs,hcoord⟩ := D.exists_smooth_selected_coordinate_test hG.1 hf hH.1 hinf' k
  have ht := E.smooth_commonPoint_trace_null_of_published_inputs hmax hsolver hprincipal hsob hcross
    hplane hcoarea hLusin hsard hsch hsep hcollar hselect hgreen harea hcompact hfinite
    hmontel hhurwitz hzero harcs hstandard hpath hdual hlift hG hinf hf hfix hH hinf' hrem hΦ hs i
  filter_upwards [ht] with y hy
  have he : ((fun x => (complexPlaneCoordinates.symm (finiteCoord
        (D.selectedTarget hG.1 hf (complexCoordinateLine i y x : Sphere)))) k) ''
        {x | complexCoordinateLine i y x ∈ D.commonPointPlane}) =
      ((fun x => D.realSelectedScalar hG.1 hf (sphereFromPlaneFunction Φ)
        (realCoordinateLine i y x)) '' {x | complexCoordinateLine i y x ∈ D.commonPointPlane}) := by
    apply image_congr
    intro x hx
    have hh := hcoord (complexCoordinateLine i y x) hx.1
    simpa only [complexCoordinateLine,ContinuousLinearEquiv.apply_symm_apply] using hh.symm
  rw [he]
  exact hy

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
