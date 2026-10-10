import OAI.Geometry.RCD.Heat.OptimalHeatCalibration

namespace OAI

/-! # A common full-measure calibration along an optimal geodesic plan -/

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

theorem optimal_plan_calibration (a₀ : S) (b₀ : T) (hK : K ≤ 0)
    (hε1 : ∀ k, ε k ≤ 1) (hε0 : Tendsto ε atTop (𝓝 0)) {R : ℝ} (hR : 0 ≤ R)
    (hdS : ∀ a : S, dist p a ≤ R) (hdT : ∀ b : T, dist p b ≤ R)
    (π : Measure C(Time,X)) (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hopt : IsOptimalCoupling (μ.map Subtype.val) (ν.map Subtype.val)
      (π.map (fun γ => (γ 0,γ 1)))) :
    ∃ A : ℝ, ∀ᵐ γ ∂π, ∀ s : Time, 0 < (s : ℝ) → (s : ℝ) < 1 →
      D.forward.potential ((s : ℝ)/2) (γ s)=
        (D.backward.potential (1/2) a₀-D.backward.potential (1/2) (γ 0))-
          (s : ℝ)*dist (γ 0) (γ 1)^2-A := by
  obtain ⟨A,hA⟩ := D.optimal_coupling_calibration a₀ b₀ hK hε1 hε0 hR hdS hdT
    (π.map (fun γ => (γ 0,γ 1))) hopt
  have hm : Measurable (fun γ : C(Time,X) => (γ 0,γ 1)) :=
    (measurable_path_eval 0).prodMk (measurable_path_eval 1)
  have hh := ae_of_ae_map hm.aemeasurable hA
  refine ⟨A,?_⟩
  filter_upwards [hgeo,hh] with γ hγ hcal
  intro s hs hs1
  have h0 : dist (γ s) (γ 0)=(s : ℝ)*dist (γ 0) (γ 1) := by
    simpa [abs_of_nonneg s.property.1] using hγ s 0
  have h1 : dist (γ s) (γ 1)=(1-(s : ℝ))*dist (γ 0) (γ 1) := by
    simpa [abs_of_nonpos (sub_nonpos.mpr s.property.2),neg_sub] using hγ s 1
  exact hcal s ⟨hs,hs1⟩ (γ s) h0 h1

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
