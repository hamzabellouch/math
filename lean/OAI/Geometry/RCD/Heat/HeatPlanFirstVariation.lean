import OAI.Geometry.RCD.Heat.HeatEnvelopeContact
import OAI.Geometry.RCD.Heat.FixedGaugeCalibration
import OAI.Geometry.RCD.Transport.CompactContactFirstVariation

namespace OAI

/-! # The actual heat envelope represents the transport velocity

On every reversed interior subpath the compact Sobolev contact potential
agrees with the prescribed heat envelope throughout the working ball.
Its minimal gradient and signed first variation are derived, not assumed.
-/

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

theorem heat_plan_first_variation (a₀ : S) (b₀ : T) (hK : K ≤ 0)
    (hε1 : ∀ k, ε k ≤ 1) (hε0 : Tendsto ε atTop (𝓝 0)) {R : ℝ} (hR : 0 ≤ R)
    (hdS : ∀ a : S, dist p a ≤ R) (hdT : ∀ b : T, dist p b ≤ R)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hopt : IsOptimalCoupling (μ.map Subtype.val) (ν.map Subtype.val)
      (π.map (fun γ => (γ 0,γ 1))))
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • hausdorff n X)
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π)
    (s : Time) (hs : 0 < (s:ℝ)) (hs1 : (s:ℝ) < 1) :
    ∃ (M : ℝ) (u : SobolevSpace (hausdorff n X) hX.quadratic),
      (∀ᵐ x ∂hausdorff n X, x ∈ closedBall p (3*R) →
        SobolevSpace.toLp (hausdorff n X) hX.quadratic u x =
          -((s:ℝ)/2)*D.forward.potential ((s:ℝ)/2) x-M) ∧
      (∀ᵐ γ ∂π, SobolevSpace.minimalSlope (hausdorff n X) hX.quadratic u (γ s) =
        dist (γ s) (γ 0)) ∧
      ∀ g : SobolevSpace (hausdorff n X) hX.quadratic,
        Tendsto (planInitialSecant (π.map (subpath s 0))
          (SobolevSpace.toLp (hausdorff n X) hX.quadratic g)) (𝓝[>] (0:ℝ))
          (𝓝 (-weightedGradientPair (hausdorff n X) hX.quadratic
            (π.map (fun γ => γ s)) u g)) := by
  have hhalf : (s:ℝ)/2 ∈ Ioo (0:ℝ) 1 := ⟨half_pos hs,by linarith⟩
  obtain ⟨M,r,ψ,L,hψ,_,hψzero,hχ,_,_,hlocal,hcontact⟩ :=
    D.forward_compact_contacts a₀ hK hε0 hR hdS hhalf (show 0 ≤ 3*R by positivity)
  have hcal := D.optimal_plan_fixed_gauge_calibration a₀ b₀ hK hε1 hε0 hR hdS hdT π hgeo hopt
  have hends := optimalPlan_endpoints (μ.map Subtype.val) (ν.map Subtype.val) π hopt
  have hS : MeasurableSet S := (isCompact_iff_compactSpace.mpr inferInstance).isClosed.measurableSet
  have hT : MeasurableSet T := (isCompact_iff_compactSpace.mpr inferInstance).isClosed.measurableSet
  have hleft : ∀ᵐ γ ∂π, ∃ a : S, a ∈ μ.support ∧ (a:X) = γ 0 := by
    apply ae_of_ae_map (μ := π) (f := fun γ : C(Time,X) => γ 0)
      (p := fun x : X => ∃ a : S, a ∈ μ.support ∧ (a:X) = x)
      (measurable_path_eval 0).aemeasurable
    rw [hends.1]
    apply (MeasurableEmbedding.subtype_coe hS).ae_map_iff.mpr
    filter_upwards [μ.support_mem_ae] with a ha
    exact ⟨a,ha,rfl⟩
  have hright : ∀ᵐ γ ∂π, dist p (γ 1) ≤ R := by
    apply ae_of_ae_map (μ := π) (f := fun γ : C(Time,X) => γ 1)
      (p := fun x : X => dist p x ≤ R) (measurable_path_eval 1).aemeasurable
    rw [hends.2]
    exact (MeasurableEmbedding.subtype_coe hT).ae_map_iff.mpr (Eventually.of_forall hdT)
  have hc : ∀ᵐ γ ∂π, hopfLax (-ψ) 1 (γ s)+ψ (γ 0) = dist (γ s) (γ 0)^2/2 := by
    filter_upwards [hleft,hright,hgeo,hcal] with γ hleft hright hγ hcal
    obtain ⟨a,ha,haeq⟩ := hleft
    have hleftR : dist p (γ 0) ≤ R := by simpa only [haeq] using hdS a
    have hlength : dist (γ 0) (γ 1) ≤ 2*R := by
      have hh := dist_triangle (γ 0) p (γ 1)
      rw [dist_comm (γ 0) p] at hh
      linarith
    have hdist : dist (γ s) (γ 0) = (s:ℝ)*dist (γ 0) (γ 1) := by
      simpa [abs_of_nonneg s.property.1] using hγ s 0
    have hball : γ s ∈ closedBall p (3*R) := by
      rw [mem_closedBall,dist_comm]
      have hh := dist_triangle p (γ 0) (γ s)
      rw [dist_comm (γ 0) (γ s),hdist] at hh
      have hmul := mul_le_mul_of_nonneg_right s.property.2 (dist_nonneg (x := γ 0) (y := γ 1))
      linarith
    have hvalue := hcal s hs hs1
    have hcost : dist (γ s) (γ 0)^2/(2*((s:ℝ)/2)) = (s:ℝ)*dist (γ 0) (γ 1)^2 := by
      rw [hdist]
      field_simp [hs.ne']
    have henv : D.forward.potential ((s:ℝ)/2) (γ s) =
        D.leftPotential a₀ a-dist (γ s) (a:X)^2/(2*((s:ℝ)/2))-
          D.forwardGauge a₀ hK hε0 hR hdS := by
      change D.forward.potential ((s:ℝ)/2) (γ s) =
        (D.backward.potential (1/2) a₀-D.backward.potential (1/2) (a:X))-
          dist (γ s) (a:X)^2/(2*((s:ℝ)/2))-D.forwardGauge a₀ hK hε0 hR hdS
      rw [haeq,hcost]
      exact hvalue
    simpa only [haeq] using hcontact (γ s) hball a ha henv
  let ρ := π.map (subpath s 0)
  have hρgeo : ∀ᵐ γ ∂ρ, IsGeodesic γ := by
    apply (ae_map_iff (subpath_measurable s 0).aemeasurable isClosed_geodesicSet.measurableSet).mpr
    exact hgeo.mono fun γ hγ => hγ.subpath s 0
  have hρcomp (t : Time) : ρ.map (fun γ => γ t) ≤ C • hausdorff n X := by
    rw [show ρ = π.map (subpath s 0) from rfl,subpath_map_eval]
    exact hcomp _
  have hρc : ∀ᵐ γ ∂ρ, hopfLax (-ψ) 1 (γ 0)+ψ (γ 1) = dist (γ 0) (γ 1)^2/2 := by
    have hχcont := hχ.continuous
    have hψcont := hψ.continuous
    have hm : MeasurableSet {γ : C(Time,X) | hopfLax (-ψ) 1 (γ 0)+ψ (γ 1) =
        dist (γ 0) (γ 1)^2/2} := (isClosed_eq (by fun_prop) (by fun_prop)).measurableSet
    apply (ae_map_iff (subpath_measurable s 0).aemeasurable hm).mpr
    simpa only [subpath_zero,subpath_one] using hc
  obtain ⟨u,hu,hgrad,hvar⟩ := compact_contact_first_variation (hausdorff n X) hX.quadratic
    hX.geodesic p hψ hψzero ρ hρgeo hC hρcomp (testPlan_subpath_length_memLp π hgeo hD s 0) hρc
  refine ⟨M,u,?_,?_,?_⟩
  · filter_upwards [hu] with x hx
    intro hxb
    exact hx.symm.trans (hlocal x hxb)
  · have hh := ae_of_ae_map (subpath_measurable s 0).aemeasurable hgrad
    simpa only [subpath_zero,subpath_one] using hh
  · intro g
    simpa only [ρ,subpath_map_eval,timeSegment_zero] using hvar g

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
