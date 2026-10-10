import OAI.Geometry.RCD.Transport.PlanEntropyDerivative

namespace OAI

/-! # The dimensional entropy subgradient on the actual optimal transport potential -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal NNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X] {K : ℝ} {n : ℕ}
  [IsLocallyFiniteMeasure (hausdorff n X)] (hX : NoncollapsedRCD K n X)
include hX
attribute [local instance] pathBorel pathBorelSpace

theorem entropic_plan_subgradient (hn : 2 ≤ n) (hK : K ≤ 0)
    {N : ℝ} (hN : (n:ℝ) ≤ N) (a : RenyiTransportNode n X)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling a.left a.right (π.map (fun γ => (γ 0,γ 1))))
    {C : ℝ≥0} (hC : 0 < C)
    (hc : ∀ t : Time, π.map (fun γ => γ t) ≤ ENNReal.ofReal C • hausdorff n X)
    (u ρ : SobolevSpace (hausdorff n X) hX.quadratic)
    {h : X → ℝ} {L : ℝ≥0} (hh : LipschitzWith L h) (hhn : ∀ x, 0 ≤ h x)
    (hi : Integrable h (hausdorff n X))
    (hrep : (SobolevSpace.toLp _ hX.quadratic ρ : X → ℝ) =ᵐ[hausdorff n X] fun x => h x^2)
    (hν : a.left=(hausdorff n X).withDensity
      (fun x => ENNReal.ofReal (SobolevSpace.toLp _ hX.quadratic ρ x)))
    {φ ψ : X → ℝ} (hu : φ =ᵐ[hausdorff n X] SobolevSpace.toLp _ hX.quadratic u)
    (had : ∀ x y, φ x+ψ y ≤ dist x y^2/2)
    (hcontact : ∀ᵐ γ ∂π, φ (γ 0)+ψ (γ 1)=dist (γ 0) (γ 1)^2/2)
    (hb : ∀ᵐ γ ∂π, SobolevSpace.minimalSlope _ hX.quadratic u (γ 0) ≤ dist (γ 0) (γ 1)) :
    -energyForm (hausdorff n X) hX.quadratic u ρ ≤
      entropyPowerRate N (-(K*(wassersteinSq a.left a.right).toReal/N))
        (Real.exp (-boltzmannEntropy (hausdorff n X) a.left/N))
        (Real.exp (-boltzmannEntropy (hausdorff n X) a.right/N)) := by
  let μ := hausdorff n X
  let : μ.Regular := inferInstance
  let r := SobolevSpace.toLp μ hX.quadratic ρ
  have hrn : (fun x => h x^2) =ᵐ[μ] fun x => (a.left.rnDeriv μ x).toReal := by
    rw [hν]
    filter_upwards [Measure.rnDeriv_withDensity μ (Lp.stronglyMeasurable r).measurable.ennreal_ofReal,
      hrep] with x hx hs
    rw [hx,hs,ENNReal.toReal_ofReal (sq_nonneg _)]
  have he := optimalPlan_endpoints a.left a.right π hp
  have hDb := a.distance_bound π inferInstance hg hp
  have hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π :=
    MemLp.of_bound ((measurable_path_eval 0).dist (measurable_path_eval 1)).aestronglyMeasurable
      a.distance (hDb.mono fun γ hh => by simpa only [Real.norm_eq_abs,abs_of_nonneg dist_nonneg] using hh)
  have hd := sqrt_core_signed_variation μ hX.quadratic π hg ENNReal.ofReal_ne_top hc hD
    a.distance_nonneg hDb u ρ hh hhn hi hrep (he.1.trans hν) hu had hcontact hb
  exact hX.entropic_plan_first_variation hn hK hN a π hg hp hC hc r hrep hrn hd

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
