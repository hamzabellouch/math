import OAI.Analysis.CircleDomains.Topology.FiniteJordanModelInput
import OAI.Analysis.CircleDomains.Selection.PublishedAppendingPair
import OAI.Analysis.CircleDomains.Uniformization.ScalarModelSequenceLimit
import OAI.Analysis.CircleDomains.Modulus.PersistentSavedBarriers

namespace OAI

/-! Select actual circle models for the recursively constructed finite
families, then extract their normalized conformal limit. The model supply
in the intermediate construction is discharged by the published-input
finite-list theorem below. -/
open Set Function Filter Metric MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace AppendingSequence
variable {G : Set Sphere} {a ε : ℝ}
variable (hsupply : FiniteAppendingSupply G a)
  (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
  (hTD : IsTotallyDisconnected Gᶜ) (ha : 0 < a)
  (hBa : {z : ℂ | (z : Sphere) ∉ G} ⊆ Metric.ball 0 a) (hε : 0 < ε)
  (T : FiniteCompactTests G)
local notation "states" => appendingStates hsupply hsard hsch hG hinf hTD ha hBa hε T

 theorem exists_models_and_limit
    (harea : ExteriorCoefficientAreaTheorem)
    (hmontel : MontelExhaustion) (hhurwitz : HurwitzUnivalentLimit)
    (hzero : HurwitzZeroFreeLimit)
    (hconn : IsConnected G)
    (hmodels : ∀ S : FiniteCompactTests G, Nonempty (CompactScalarCircleModel G S.test)) :
    ∃ M : ∀ n, CompactScalarCircleModel G (states n).family.test,
      ∃ (s : ℕ → ℕ) (F : ℂ → ℂ), StrictMono s ∧
        TendstoLocallyUniformlyOn (fun n => (M (s n)).function) F atTop
          {z : ℂ | (z : Sphere) ∈ G} ∧
        IsPrincipalNormalized (extendAtInfinity F) ∧
        IsConformalEquivalence (extendAtInfinity F) G (extendAtInfinity F '' G) := by
  let M := fun n => Classical.choice (hmodels (states n).family)
  obtain ⟨s,F,hs,hlim,hnorm,hconf⟩ := scalar_models_conformal_limit
    harea hmontel hhurwitz hzero hG hconn hinf ha hBa (fun n => (states n).family) M
  exact ⟨M,s,F,hs,hlim,hnorm,hconf⟩

end AppendingSequence
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

theorem exists_recursive_models_of_published_inputs
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
    (hBne : {z : ℂ | (z : Sphere) ∉ G}.Nonempty)
    {ε : ℝ} (hε : 0 < ε) (T : FiniteCompactTests G) :
    ∃ hsupply : FiniteAppendingSupply G a,
      let states := appendingStates hsupply hsard hsch hG hinf hTD ha hBa hε T
      ∃ M : ∀ n, CompactScalarCircleModel G (states n).family.test,
        ∃ (s : ℕ → ℕ) (F : ℂ → ℂ), StrictMono s ∧
          TendstoLocallyUniformlyOn (fun n => (M (s n)).function) F atTop
            {z : ℂ | (z : Sphere) ∈ G} ∧
          IsPrincipalNormalized (extendAtInfinity F) ∧
          IsConformalEquivalence (extendAtInfinity F) G (extendAtInfinity F '' G) := by
  let hsupply := finiteAppendingSupply_of_published_inputs hsolver hprincipal hsob hcross hplane
    hcoarea hLusin hsard hsch hsep hcollar hselect hgreen harea hcompact hfinite
    hmontel hhurwitz hzero harcs hstandard hpath hdual hlift hG hconn hinf hTD ha hBa hBne
  refine ⟨hsupply, ?_⟩
  apply AppendingSequence.exists_models_and_limit hsupply hsard hsch hG hinf hTD
    ha hBa hε T harea hmontel hhurwitz hzero hconn
  intro S
  exact exists_signed_compact_scalar_circle_model hcross hplane hcoarea hLusin hsard hsch hsep hcollar hselect hgreen harea hcompact hfinite hmontel hhurwitz hzero
    harcs hstandard hpath hdual hlift hG hconn hinf hTD S.test S.continuous S.compact
    S.witness S.pair_null

end CircleDomainRigidity

end

end OAI
