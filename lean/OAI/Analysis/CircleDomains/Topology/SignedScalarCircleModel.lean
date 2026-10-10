import OAI.Analysis.CircleDomains.Topology.FiniteJordanModelInput
import OAI.Analysis.CircleDomains.Topology.ContinuousScalarCircleModel
import OAI.Analysis.CircleDomains.Selection.SignedTestFamily
import OAI.Analysis.CircleDomains.Transfer.ScalarModelLinearRecovery
import OAI.Analysis.CircleDomains.Transfer.EmptyDustScalarModel

namespace OAI

/-! Finite signed compact tests have a common circle model. The proof
uses the proved unit-test construction, and recovers all original tests
by an exact linear combination on the same model. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

theorem exists_signed_compact_scalar_circle_model
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
    Nonempty (CompactScalarCircleModel G u) := by
  classical
  by_cases hBne : Gᶜ.Nonempty
  · obtain ⟨T⟩ := exists_signed_test_family hG hinf u hu hs H hpair
    obtain ⟨M⟩ := exists_compact_scalar_circle_model hcross hplane hcoarea hLusin hsard hsch hsep hcollar hselect hgreen harea hcompact hfinite hmontel hhurwitz hzero
      harcs hstandard hpath hdual hlift hG hconn hinf hTD hBne
      T.test T.continuous T.compact T.unit T.witness T.pair_null
    have he : (fun i x => (2 * T.scale i) * T.test i.succ x - T.scale i * T.test 0 x) = u := by
      funext i x
      exact T.recovery i x
    rw [← he]
    exact ⟨M.linearDifference Fin.succ (fun _ => 0) (fun i => 2 * T.scale i) T.scale⟩
  · have hGu : G = univ := by
      apply eq_univ_of_forall
      intro p
      by_contra hp
      exact hBne ⟨p, hp⟩
    subst G
    have hphys : physicalPlaneDomain (univ : Set Sphere) = univ := rfl
    exact ⟨compactScalarCircleModel_identity u (fun i => hphys ▸ H i)⟩

end CircleDomainRigidity

end

end OAI
