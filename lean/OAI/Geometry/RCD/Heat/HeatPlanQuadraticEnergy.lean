import OAI.Geometry.RCD.Heat.HeatPlanWeakVelocity

namespace OAI

/-! # The heat action's exact energy on an optimal geodesic plan -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X}
  {hn : 2 ≤ n} {p : X} [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]
  {S T : Set X} [CompactSpace S] [CompactSpace T]
  {μ : Measure S} {ν : Measure T} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ε : ℕ → ℝ} {hε : ∀ k, 0 < ε k}
  (D : hX.CompactHeatScalingData hn p μ ν ε hε)
attribute [local instance] pathBorel pathBorelSpace

theorem heat_plan_quadratic_energy (a₀ : S) (b₀ : T) (hK : K ≤ 0)
    (hε1 : ∀ k, ε k ≤ 1) (hε0 : Tendsto ε atTop (𝓝 0)) {R : ℝ} (hR : 0 < R)
    (hS : ∀ a : S, dist p a ≤ R) (hT : ∀ b : T, dist p b ≤ R)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hopt : IsOptimalCoupling (μ.map Subtype.val) (ν.map Subtype.val)
      (π.map (fun γ => (γ 0,γ 1))))
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • hausdorff n X)
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π)
    (s : Time) (hs : 0 < (s:ℝ)) (hs1 : (s:ℝ) < 1)
    (v : SobolevSpace (hausdorff n X) hX.quadratic)
    (hv : SobolevSpace.toLp (hausdorff n X) hX.quadratic v
      =ᵐ[(hausdorff n X).restrict (closedBall p (6*R))] D.forward.potential ((s:ℝ)/2)) :
    (∫ x in closedBall p (6*R), radialCutoff p (3*R) x*
      localGamma (hausdorff n X) hX.quadratic v v x ∂π.map (fun γ => γ s))
      = 4*∫ γ, dist (γ 0) (γ 1)^2 ∂π := by
  let m := hausdorff n X
  let q := hX.quadratic
  let η := π.map (fun γ => γ s)
  have hv' : ∀ᵐ x ∂m, x∈closedBall p (3*R) → SobolevSpace.toLp m q v x=
      D.forward.potential ((s:ℝ)/2) x := by
    filter_upwards [(ae_restrict_iff' measurableSet_closedBall).mp hv] with x hx hm
    exact hx ((closedBall_subset_closedBall (by linarith)) hm)
  obtain ⟨hgrad,-⟩ := D.heat_plan_weak_velocity_of_representative a₀ b₀ hK hε1 hε0 hR.le
    hS hT π hgeo hopt hC hcomp hD s hs hs1 v hv'
  have hends := optimalPlan_endpoints (μ.map Subtype.val) (ν.map Subtype.val) π hopt
  have hSm : MeasurableSet S := (isCompact_iff_compactSpace.mpr inferInstance).isClosed.measurableSet
  have hTm : MeasurableSet T := (isCompact_iff_compactSpace.mpr inferInstance).isClosed.measurableSet
  have hend (t : Time) (ρ : Measure X) (heq : π.map (fun γ => γ t) = ρ)
      (hb : ∀ᵐ x ∂ρ, dist p x ≤ R) : ∀ᵐ γ ∂π, dist p (γ t) ≤ R := by
    apply ae_of_ae_map (μ := π) (f := fun γ : C(Time,X) => γ t)
      (p := fun x : X => dist p x ≤ R) (measurable_path_eval t).aemeasurable
    rwa [heq]
  have h0 := hend 0 (μ.map Subtype.val) hends.1
    ((MeasurableEmbedding.subtype_coe hSm).ae_map_iff.mpr (Eventually.of_forall hS))
  have h1 := hend 1 (ν.map Subtype.val) hends.2
    ((MeasurableEmbedding.subtype_coe hTm).ae_map_iff.mpr (Eventually.of_forall hT))
  have hstay := geodesic_plan_eval_ball π hgeo p h0 h1 s
  have hac : η ≪ m := Measure.absolutelyContinuous_of_le_smul (hcomp s)
  have hself := ae_of_ae_map (measurable_path_eval s).aemeasurable
    ((localGamma_self m q v).filter_mono hac.ae_le)
  have hφ : (fun x => radialCutoff p (3*R) x*localGamma m q v v x)
      =ᵐ[η] localGamma m q v v := by
    filter_upwards [hstay] with x hx
    rw [radialCutoff_eq_one p (by positivity) (by simpa only [mem_closedBall,dist_comm] using hx),one_mul]
  have hstay' : ∀ᵐ x ∂η, x∈closedBall p (6*R) :=
    hstay.mono fun x hx => (closedBall_subset_closedBall (by linarith)) hx
  rw [Measure.restrict_eq_self_of_ae_mem hstay',integral_congr_ae hφ]
  rw [integral_map (measurable_path_eval s).aemeasurable
    ((localGamma_memL1 m q v v).aestronglyMeasurable.mono_ac hac)]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hself,hgrad] with γ he hg
  rw [he,hg]
  ring

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
