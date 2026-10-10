import OAI.Analysis.CircleDomains.Topology.FiniteJordanModelInput
import OAI.Analysis.CircleDomains.Sobolev.TrackedGlobalWeakLimit
import OAI.Analysis.CircleDomains.Topology.RecursiveCircleModels

namespace OAI

/-! Compact continuous Sobolev functions extend across removable dust.
The approximate global gradients come from the actual recursive finite
models, and a second weak limit removes the approximation error. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

theorem dust_sobolev_extension_of_published_inputs
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
    (hrem : IsConformallyRemovable Gᶜ)
    {u : EuclideanPlane → ℝ} (hu : Continuous u) (hs : HasCompactSupport u)
    (W : DeGiorgi.MemW1pWitness 2 u (physicalPlaneDomain G)) :
    ∃ V : DeGiorgi.MemW1pWitness 2 u univ,
      (∫ x, ‖V.weakGrad x‖^2) ≤ (‖W.weakGrad_memLp.toLp W.weakGrad‖+1)^2 := by
  let N := ‖W.weakGrad_memLp.toLp W.weakGrad‖
  let e := fun n : ℕ => 1/((n:ℝ)+1)
  have hepos (n : ℕ) : 0 < e n := by dsimp only [e]; positivity
  have hele (n : ℕ) : e n ≤ 1 := by
    dsimp only [e]
    apply (div_le_one (by positivity)).mpr
    have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have het : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let T := FiniteCompactTests.singleton u hu hs W
  have hap (n : ℕ) : ∃ (v : C(Sphere,ℝ)) (g : EuclideanPlane → EuclideanPlane),
      (∀ p, |v p-sphereFromPlaneFunction u p| ≤ e n/4) ∧
      MemLp g 2 volume ∧ DeGiorgi.HasWeakGrad g (fun x => v (planeSphere x)) univ ∧
      (∫ x, ‖g x‖^2) ≤ (N+e n/4)^2 := by
    obtain ⟨hsupply,M,σ,F,hσ,hlim,hnorm,hF⟩ := exists_recursive_models_of_published_inputs
      hsolver hprincipal hsob hcross hplane hcoarea hLusin hsard hsch hsep hcollar hselect
      hgreen harea hcompact hfinite hmontel hhurwitz hzero harcs hstandard hpath hdual hlift
      hG hconn hinf hTD ha hBa hBne (hepos n) T
    exact AppendingSequence.exists_tracked_global_weak_limit hsupply hsard hsch hG hinf hTD
      ha hBa (hepos n) T hprincipal harea hconn hrem M hσ hnorm hF hlim (0 : Fin 1)
  choose v g hclose hg hw hE using hap
  have hvcont (n : ℕ) : Continuous (fun x => v n (planeSphere x)) :=
    (v n).continuous.comp continuous_planeSphere
  obtain ⟨C,hC⟩ := hu.bounded_above_of_compact_support hs
  have hbound (n : ℕ) (x : EuclideanPlane) : ‖v n (planeSphere x)‖ ≤ C+1 := by
    have hh : |v n (planeSphere x)-u x| ≤ e n/4 := by
      simpa only [planeSphere,sphereFromPlaneFunction_coe,complexPlaneCoordinates.symm_apply_apply]
        using hclose n (planeSphere x)
    calc
      _ = ‖(v n (planeSphere x)-u x)+u x‖ := by congr 1; ring
      _ ≤ ‖v n (planeSphere x)-u x‖+‖u x‖ := norm_add_le _ _
      _ ≤ e n/4+C := add_le_add (by simpa only [Real.norm_eq_abs] using hh) (hC x)
      _ ≤ C+1 := by linarith [hele n]
  have hp (x : EuclideanPlane) :
      Tendsto (fun n => v n (planeSphere x)) atTop (𝓝 (u x)) := by
    apply Metric.tendsto_atTop.mpr
    intro δ hδ
    have ht : Tendsto (fun n => e n/4) atTop (𝓝 0) := by simpa using het.div_const 4
    obtain ⟨n,hn⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hδ))
    refine ⟨n,fun k hk => ?_⟩
    have hh : |v k (planeSphere x)-u x| ≤ e k/4 := by
      simpa only [planeSphere,sphereFromPlaneFunction_coe,complexPlaneCoordinates.symm_apply_apply]
        using hclose k (planeSphere x)
    simpa only [Real.dist_eq] using hh.trans_lt (hn k hk)
  have henergy (n : ℕ) : (∫ x, ‖g n x‖^2) ≤ (N+1)^2 := by
    apply (hE n).trans
    have hN : 0 ≤ N := norm_nonneg _
    have hnp : 0 ≤ N+e n/4 := by positivity
    gcongr
    linarith [hele n]
  obtain ⟨G,hGmem,hGweak,hGE⟩ := exists_bounded_energy_weak_gradient g hg hw hvcont hbound
    (Eventually.of_forall hp) henergy
  let V : DeGiorgi.MemW1pWitness 2 u univ := {
    memLp := by simpa only [Measure.restrict_univ] using hu.memLp_of_hasCompactSupport hs
    weakGrad := G
    weakGrad_component_memLp := fun i => by
      simpa only [Measure.restrict_univ] using memLp_piLp_iff.mp hGmem i
    isWeakGrad := hGweak }
  exact ⟨V,hGE⟩

end CircleDomainRigidity

end

end OAI
