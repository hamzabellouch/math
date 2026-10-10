import OAI.Geometry.RCD.Heat.OptimalHeatPlanCalibration

namespace OAI

/-! # An actual bounded-compression RCD plan calibrated by the heat limit -/

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

theorem exists_calibrated_plan (a₀ : S) (b₀ : T) (hK : K ≤ 0)
    (hε1 : ∀ k, ε k ≤ 1) (hε0 : Tendsto ε atTop (𝓝 0)) {R : ℝ} (hR : 0 ≤ R)
    (hdS : ∀ a : S, dist p a ≤ R) (hdT : ∀ b : T, dist p b ≤ R)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hμ : μ.map Subtype.val ≤ C • hausdorff n X)
    (hν : ν.map Subtype.val ≤ C • hausdorff n X) :
    ∃ (π : Measure C(Time,X)) (A : ℝ), IsProbabilityMeasure π ∧
      (∀ᵐ γ ∂π, IsGeodesic γ) ∧
      IsOptimalCoupling (μ.map Subtype.val) (ν.map Subtype.val) (π.map (fun γ => (γ 0,γ 1))) ∧
      Integrable (fun γ : C(Time,X) => dist (γ 0) (γ 1)^2) π ∧
      (∀ t : Time, π.map (fun γ => γ t) ≤ compressionBudget K n (2*R) C • hausdorff n X) ∧
      ∀ᵐ γ ∂π, ∀ s : Time, 0 < (s : ℝ) → (s : ℝ) < 1 →
        D.forward.potential ((s : ℝ)/2) (γ s)=
          (D.backward.potential (1/2) a₀-D.backward.potential (1/2) (γ 0))-
            (s : ℝ)*dist (γ 0) (γ 1)^2-A := by
  have hS : MeasurableSet S := (isCompact_iff_compactSpace.mpr inferInstance).isClosed.measurableSet
  have hT : MeasurableSet T := (isCompact_iff_compactSpace.mpr inferInstance).isClosed.measurableSet
  have hs0 : ∀ᵐ x ∂μ.map Subtype.val, dist x p ≤ R :=
    (MeasurableEmbedding.subtype_coe hS).ae_map_iff.mpr (Eventually.of_forall fun a => by
      rw [dist_comm]
      exact hdS a)
  have hs1 : ∀ᵐ x ∂ν.map Subtype.val, dist x p ≤ R :=
    (MeasurableEmbedding.subtype_coe hT).ae_map_iff.mpr (Eventually.of_forall fun b => by
      rw [dist_comm]
      exact hdT b)
  obtain ⟨π,hπ,hgeo,hopt,hi,hall⟩ := hX.exists_bounded_entropy_plan K n hn
    (μ.map Subtype.val) (ν.map Subtype.val) hC hμ hν p hR hs0 hs1
  obtain ⟨A,hA⟩ := D.optimal_plan_calibration a₀ b₀ hK hε1 hε0 hR hdS hdT π hgeo hopt
  exact ⟨π,A,hπ,hgeo,hopt,hi,fun t => (hall t).1,hA⟩

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
