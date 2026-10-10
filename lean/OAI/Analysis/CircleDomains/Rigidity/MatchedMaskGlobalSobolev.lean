import OAI.Analysis.CircleDomains.Topology.FiniteJordanModelInput
import OAI.Analysis.CircleDomains.Rigidity.MatchedRealMaskSobolev
import OAI.Analysis.CircleDomains.Sobolev.DustSobolevExtension

namespace OAI

/-! The constructed matched masks extend across their actual residual
removable dust. All conditional inputs are exactly those of the proved
dust Sobolev theorem; no trace or extension conclusion is assumed. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} {D : MatchedConformalEnds G f}
variable [Encodable D.IndexedMatchedPair]

 theorem MatchedRealMask.global_sobolev_of_published_inputs
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
    {E : D.MatchedRoundDisks} {hG : IsOpen G} {hf : IsConformalEquivalence f G (f '' G)}
    {φ : Sphere → ℝ} {L : ℝ≥0} {m : ℕ} (M : MatchedRealMask E hG hf φ L m)
    (hinf : OnePoint.infty ∈ G)
    (hb : ContDiffOn ℝ 1 (D.realSelectedScalar hG hf φ) (realPlaneDomain G))
    (hb2 : MemLp (fderiv ℝ (D.realSelectedScalar hG hf φ)) 2 (volume.restrict (realPlaneDomain G))) :
    Nonempty (DeGiorgi.MemW1pWitness 2
      (D.realMaskValue E hG hf φ L M.cutoff ∘ euclideanPlaneCoordinates) univ) := by
  let O := maskDomain G M.neighborhood
  obtain ⟨H⟩ := M.sobolev hb hb2
  have hi : OnePoint.infty ∈ O := Or.inl hinf
  have hu : Continuous (D.realMaskValue E hG hf φ L M.cutoff ∘ euclideanPlaneCoordinates) :=
    M.continuous.comp euclideanPlaneCoordinates.continuous
  have hus : HasCompactSupport (D.realMaskValue E hG hf φ L M.cutoff ∘ euclideanPlaneCoordinates) :=
    M.compact.comp_homeomorph euclideanPlaneCoordinates.toHomeomorph
  by_cases hempty : Oᶜ = ∅
  · have he : O = univ := by
      apply Set.eq_univ_of_forall
      intro q
      by_contra hq
      have hq' : q ∈ Oᶜ := hq
      rw [hempty] at hq'
      exact hq'
    simpa only [O,he,physicalPlaneDomain,preimage_univ] using (show Nonempty
      (DeGiorgi.MemW1pWitness 2 (D.realMaskValue E hG hf φ L M.cutoff ∘ euclideanPlaneCoordinates)
        (physicalPlaneDomain O)) from ⟨H⟩)
  · have hne : {z : ℂ | (z : Sphere) ∉ O}.Nonempty := by
      obtain ⟨q,hq⟩ := Set.nonempty_iff_ne_empty.mpr hempty
      cases q using OnePoint.rec with
      | infty => exact (hq hi).elim
      | coe z => exact ⟨z,hq⟩
    obtain ⟨a,ha,hbound⟩ := ((OnePoint.isOpen_iff_of_mem hi).mp M.domain_open).2.isBounded.exists_pos_norm_lt
    obtain ⟨V,_⟩ := dust_sobolev_extension_of_published_inputs hsolver hprincipal hsob hcross hplane
      hcoarea hLusin hsard hsch hsep hcollar hselect hgreen harea hcompact hfinite hmontel
      hhurwitz hzero harcs hstandard hpath hdual hlift M.domain_open M.domain_connected hi M.domain_dust
      ha (fun z hz => by simpa only [mem_ball,dist_zero_right] using hbound z hz)
      hne M.domain_removable hu hus H
    exact ⟨V⟩

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
