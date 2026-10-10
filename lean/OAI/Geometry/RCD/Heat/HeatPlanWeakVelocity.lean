import OAI.Geometry.RCD.Heat.HeatPlanFirstVariation
import OAI.Geometry.RCD.Transport.SubpathMeanVariation
import OAI.Geometry.RCD.Harmonic.LocalVelocityIdentification
import OAI.Geometry.RCD.Heat.LocalHeatRepresentative
import OAI.Geometry.RCD.Transport.BoundedGeodesicPlan

namespace OAI

/-! # Physical-time weak velocity of the actual heat limit

The local heat representative has gradient length twice the metric speed.
Its gradient pairing gives the signed physical-time mean variation.
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

theorem heat_plan_weak_velocity_of_representative (a₀ : S) (b₀ : T) (hK : K ≤ 0)
    (hε1 : ∀ k, ε k ≤ 1) (hε0 : Tendsto ε atTop (𝓝 0)) {R : ℝ} (hR : 0 ≤ R)
    (hdS : ∀ a : S, dist p a ≤ R) (hdT : ∀ b : T, dist p b ≤ R)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hopt : IsOptimalCoupling (μ.map Subtype.val) (ν.map Subtype.val)
      (π.map (fun γ => (γ 0,γ 1))))
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • hausdorff n X)
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π)
    (s : Time) (hs : 0 < (s:ℝ)) (hs1 : (s:ℝ) < 1)
    (v : SobolevSpace (hausdorff n X) hX.quadratic)
    (hv : ∀ᵐ x ∂hausdorff n X, x ∈ closedBall p (3*R) →
      SobolevSpace.toLp (hausdorff n X) hX.quadratic v x =
        D.forward.potential ((s:ℝ)/2) x) :
      (∀ᵐ γ ∂π, SobolevSpace.minimalSlope (hausdorff n X) hX.quadratic v (γ s) =
        2*dist (γ 0) (γ 1)) ∧
      ∀ g : SobolevSpace (hausdorff n X) hX.quadratic,
        Tendsto (fun h : ℝ => (∫ γ : C(Time,X),
          SobolevSpace.toLp (hausdorff n X) hX.quadratic g (γ s)-
          SobolevSpace.toLp (hausdorff n X) hX.quadratic g
            (geodesicExtension γ ((s:ℝ)-h)) ∂π)/h)
          (𝓝[>] (0:ℝ)) (𝓝 (-(1/2)*(∫ x, localGamma (hausdorff n X)
            hX.quadratic v g x ∂π.map (fun γ => γ s)))) := by
  obtain ⟨M,u,hu,hgrad,hvar⟩ :=
    D.heat_plan_first_variation a₀ b₀ hK hε1 hε0 hR hdS hdT π hgeo hopt hC hcomp hD s hs hs1
  have hends := optimalPlan_endpoints (μ.map Subtype.val) (ν.map Subtype.val) π hopt
  have hS : MeasurableSet S := (isCompact_iff_compactSpace.mpr inferInstance).isClosed.measurableSet
  have hT : MeasurableSet T := (isCompact_iff_compactSpace.mpr inferInstance).isClosed.measurableSet
  have hend (t : Time) (ρ : Measure X) (heq : π.map (fun γ => γ t) = ρ)
      (hb : ∀ᵐ x ∂ρ, dist p x ≤ R) : ∀ᵐ γ ∂π, dist p (γ t) ≤ R := by
    apply ae_of_ae_map (μ := π) (f := fun γ : C(Time,X) => γ t)
      (p := fun x : X => dist p x ≤ R) (measurable_path_eval t).aemeasurable
    rwa [heq]
  have h0 := hend 0 (μ.map Subtype.val) hends.1
    ((MeasurableEmbedding.subtype_coe hS).ae_map_iff.mpr (Eventually.of_forall hdS))
  have h1 := hend 1 (ν.map Subtype.val) hends.2
    ((MeasurableEmbedding.subtype_coe hT).ae_map_iff.mpr (Eventually.of_forall hdT))
  let η := π.map (fun γ => γ s)
  have hηball : ∀ᵐ x ∂η, x ∈ closedBall p (3*R) := geodesic_plan_eval_ball π hgeo p h0 h1 s
  have hac : η ≪ hausdorff n X := Measure.absolutelyContinuous_of_le_smul (hcomp s)
  have huv : ∀ᵐ x ∂η, SobolevSpace.toLp (hausdorff n X) hX.quadratic u x =
      -((s:ℝ)/2)*SobolevSpace.toLp (hausdorff n X) hX.quadratic v x-M := by
    filter_upwards [hu.filter_mono hac.ae_le,hv.filter_mono hac.ae_le,hηball] with x hu hv hx
    rw [hv hx]
    exact hu hx
  have hvgrad := scaled_contact_gradient_ratio (hausdorff n X) hX.quadratic hac u v hs huv
  have hvpath := ae_of_ae_map (measurable_path_eval s).aemeasurable hvgrad
  refine ⟨?_,?_⟩
  · filter_upwards [hvpath,hgrad,hgeo] with γ hv hu hγ
    rw [hv,hu]
    have hdist : dist (γ s) (γ 0) = (s:ℝ)*dist (γ 0) (γ 1) := by
      simpa [abs_of_nonneg s.property.1] using hγ s 0
    rw [hdist]
    field_simp
  · intro g
    have hg := (Lp.stronglyMeasurable (SobolevSpace.toLp (hausdorff n X) hX.quadratic g)).measurable
    have hm := reverse_subpath_mean_limit π hg s hs (hvar g)
    simp only [neg_neg] at hm
    rw [scaled_contact_velocity_pair (hausdorff n X) hX.quadratic hC (hcomp s) u v g hs huv] at hm
    exact hm

theorem heat_plan_weak_velocity (a₀ : S) (b₀ : T) (hK : K ≤ 0)
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
    ∃ v : SobolevSpace (hausdorff n X) hX.quadratic,
      (∀ᵐ x ∂hausdorff n X, x ∈ closedBall p (3*R) →
        SobolevSpace.toLp (hausdorff n X) hX.quadratic v x =
          D.forward.potential ((s:ℝ)/2) x) ∧
      (∀ᵐ γ ∂π, SobolevSpace.minimalSlope (hausdorff n X) hX.quadratic v (γ s) =
        2*dist (γ 0) (γ 1)) ∧
      ∀ g : SobolevSpace (hausdorff n X) hX.quadratic,
        Tendsto (fun h : ℝ => (∫ γ : C(Time,X),
          SobolevSpace.toLp (hausdorff n X) hX.quadratic g (γ s)-
          SobolevSpace.toLp (hausdorff n X) hX.quadratic g
            (geodesicExtension γ ((s:ℝ)-h)) ∂π)/h)
          (𝓝[>] (0:ℝ)) (𝓝 (-(1/2)*(∫ x, localGamma (hausdorff n X)
            hX.quadratic v g x ∂π.map (fun γ => γ s)))) := by
  obtain ⟨_,u,hu,_,_⟩ :=
    D.heat_plan_first_variation a₀ b₀ hK hε1 hε0 hR hdS hdT π hgeo hopt hC hcomp hD s hs hs1
  obtain ⟨v,hv⟩ := local_heat_representative (hausdorff n X) hX.quadratic p
    (show 0 ≤ 3*R by positivity) hs u (D.forward.potential ((s:ℝ)/2)) hu
  refine ⟨v,hv,?_⟩
  exact D.heat_plan_weak_velocity_of_representative a₀ b₀ hK hε1 hε0 hR hdS hdT
    π hgeo hopt hC hcomp hD s hs hs1 v hv

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
