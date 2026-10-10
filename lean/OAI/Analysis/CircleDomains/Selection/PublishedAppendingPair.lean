import OAI.Analysis.CircleDomains.Topology.FiniteJordanModelInput
import OAI.Analysis.CircleDomains.Topology.SignedScalarCircleModel
import OAI.Analysis.CircleDomains.Topology.CompactScalarModelFromCircle
import OAI.Analysis.CircleDomains.Selection.AppendingPairData
import OAI.Analysis.CircleDomains.Topology.FiniteCompactTests

namespace OAI

/-! Finite appending pairs obtained from finite-list conformal models. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

theorem exists_appending_pair_of_published_inputs
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
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    {m : ℕ} (u : Fin m → EuclideanPlane → ℝ)
    (hu : ∀ i, Continuous (u i)) (hs : ∀ i, HasCompactSupport (u i))
    (H : ∀ i, DeGiorgi.MemW1pWitness 2 (u i) (physicalPlaneDomain G))
    (hpair : ∀ i j, i ≠ j → volume
      ((fun p => (sphereFromPlaneFunction (u i) p, sphereFromPlaneFunction (u j) p)) '' Gᶜ) = 0) :
    ∀ {a δ η : ℝ}, 0 < a → 0 < δ → 0 < η →
      {z : ℂ | (z : Sphere) ∉ G} ⊆ ball 0 a →
      {z : ℂ | (z : Sphere) ∉ G}.Nonempty →
      Nonempty (AppendingPairData G u H a δ η) := by
  intro a δ η ha hδ hη hBa hBne
  have hsource : (((↑) : ℂ → Sphere) '' ball 0 a)ᶜ ⊆ G := by
    intro p hp
    by_contra hpG
    cases p using OnePoint.rec with
    | infty => exact hpG hinf
    | coe z => exact hp ⟨z,hBa hpG,rfl⟩
  have hB : IsCompact {z : ℂ | (z : Sphere) ∉ G} :=
    isCompact_finite_preimage hG.isClosed_compl (not_not.mpr hinf)
  have hmodel := exists_signed_compact_scalar_circle_model hcross hplane hcoarea hLusin
    hsard hsch hsep hcollar hselect hgreen harea hcompact hfinite hmontel hhurwitz hzero
    harcs hstandard hpath hdual hlift hG hconn hinf hTD u hu hs H hpair
  exact exists_appending_pair_data hsolver hprincipal hgreen harea hsard hsch hsob
    hG hconn hinf hTD hB hBne hu hs H hpair
    (nonempty_compactScalarModel_of_circle hG hinf hs hmodel) ha hδ hη hBa hsource

theorem finiteAppendingSupply_of_published_inputs
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
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    {a : ℝ} (ha : 0 < a) (hBa : {z : ℂ | (z : Sphere) ∉ G} ⊆ ball 0 a)
    (hBne : {z : ℂ | (z : Sphere) ∉ G}.Nonempty) : FiniteAppendingSupply G a := by
  intro T δ η hδ hη
  exact exists_appending_pair_of_published_inputs hsolver hprincipal hsob hcross hplane hcoarea hLusin
    hsard hsch hsep hcollar hselect hgreen harea hcompact hfinite hmontel hhurwitz hzero
    harcs hstandard hpath hdual hlift hG hconn hinf hTD T.test T.continuous T.compact
    T.witness T.pair_null ha hδ hη hBa hBne

end CircleDomainRigidity

end

end OAI
