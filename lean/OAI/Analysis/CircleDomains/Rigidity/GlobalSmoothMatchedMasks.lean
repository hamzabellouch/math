import OAI.Analysis.CircleDomains.Topology.FiniteJordanModelInput
import OAI.Analysis.CircleDomains.Rigidity.SmoothMatchedScalar
import OAI.Analysis.CircleDomains.Rigidity.MatchedRealMaskConstruction
import OAI.Analysis.CircleDomains.Rigidity.MatchedMaskGlobalSobolev

namespace OAI

/-! Every compact smooth target test has an actual countable family of
global Sobolev masks. The scalar, its energy, the open domain and the
removable residual dust have all been constructed. -/
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

 theorem MatchedRoundDisks.exists_global_smooth_masks (E : D.MatchedRoundDisks)
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
    {Φ : EuclideanPlane → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (hs : HasCompactSupport Φ) :
    ∃ L : ℝ≥0, ∀ m : ℕ, ∃ M : MatchedRealMask E hG.1 hf (sphereFromPlaneFunction Φ) L m,
      Nonempty (DeGiorgi.MemW1pWitness 2
        (D.realMaskValue E hG.1 hf (sphereFromPlaneFunction Φ) L M.cutoff ∘ euclideanPlaneCoordinates) univ) := by
  obtain ⟨hφ,hφzero,L,hL⟩ := smooth_compact_sphere_scalar hΦ hs
  obtain ⟨hb,hb2⟩ := D.smooth_selected_scalar_finite_energy hG.1 hH.1 hinf hf hfix hΦ hs
  refine ⟨L,fun m => ?_⟩
  obtain ⟨M⟩ := E.exists_real_mask hmax hG hinf hf hfix hH hinf' hrem hφ hL hφzero m
  exact ⟨M,M.global_sobolev_of_published_inputs hsolver hprincipal hsob hcross hplane hcoarea hLusin
    hsard hsch hsep hcollar hselect hgreen harea hcompact hfinite hmontel hhurwitz hzero
    harcs hstandard hpath hdual hlift hinf hb hb2⟩

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
