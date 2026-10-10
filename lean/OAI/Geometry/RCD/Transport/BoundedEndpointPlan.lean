import OAI.Geometry.RCD.Harmonic.DefectSegment

namespace OAI

/-! # Actual compressed optimal plans between positive bounded endpoint sets -/

open Set Filter Metric MeasureTheory
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.bounded_endpoint_plan {n : ℕ} (hX : NoncollapsedRCD 0 n X)
    (hn : 2 ≤ n) (p : X) {R : ℝ} (hR : 0 < R) {A B : Set X}
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hA0 : hausdorff n X A ≠ 0) (hB0 : hausdorff n X B ≠ 0)
    (hsA : A ⊆ closedBall p R) (hsB : B ⊆ closedBall p R) :
    ∃ π : Measure C(Time,X), IsProbabilityMeasure π ∧ ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      (∀ᵐ γ ∂π, IsGeodesic γ) ∧
      IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
        (π.map (fun γ => (γ 0,γ 1))) ∧
      (∀ t : Time, π.map (fun γ => γ t) ≤ C • hausdorff n X) ∧
      (∀ᵐ γ ∂π, γ 0 ∈ A ∧ γ 1 ∈ B ∧ ∀ t : Time, dist (γ t) p ≤ 3*R) ∧
      (∀ᵐ x ∂π.map (fun γ => γ 0), dist x p ≤ R) ∧
      (∀ᵐ x ∂π.map (fun γ => γ 1), dist x p ≤ R) := by
  let μ := hausdorff n X
  let C : ℝ≥0∞ := max (μ A)⁻¹ (μ B)⁻¹
  have hAt : μ A ≠ ∞ := (hX.finiteOnBounded A (isBounded_closedBall.subset hsA)).ne
  have hBt : μ B ≠ ∞ := (hX.finiteOnBounded B (isBounded_closedBall.subset hsB)).ne
  have hC : C ≠ ∞ := max_ne_top (ENNReal.inv_ne_top.mpr hA0) (ENNReal.inv_ne_top.mpr hB0)
  let := uniformOn_probability μ A hA0 hAt
  let := uniformOn_probability μ B hB0 hBt
  have hbA : ∀ᵐ x ∂uniformOn μ A, dist x p ≤ R :=
    (uniformOn_ae_mem μ A hA).mono fun _ hx => hsA hx
  have hbB : ∀ᵐ x ∂uniformOn μ B, dist x p ≤ R :=
    (uniformOn_ae_mem μ B hB).mono fun _ hx => hsB hx
  obtain ⟨π,hπ,hgeo,hopt,_hi,hall⟩ := hX.exists_bounded_entropy_plan 0 n hn
    (uniformOn μ A) (uniformOn μ B) hC (uniformOn_le_scaled μ A (le_max_left _ _))
    (uniformOn_le_scaled μ B (le_max_right _ _)) p hR.le hbA hbB
  let := hπ
  have hend := optimalPlan_endpoints (uniformOn μ A) (uniformOn μ B) π hopt
  have hpaths := optimal_geodesic_plan_bounded (uniformOn μ A) (uniformOn μ B)
    π hgeo hopt p hR.le hbA hbB
  have hstart : ∀ᵐ γ ∂π, γ 0 ∈ A := by
    apply ae_of_ae_map (measurable_path_eval 0).aemeasurable
    rw [hend.1]
    exact uniformOn_ae_mem μ A hA
  have hfinish : ∀ᵐ γ ∂π, γ 1 ∈ B := by
    apply ae_of_ae_map (measurable_path_eval 1).aemeasurable
    rw [hend.2]
    exact uniformOn_ae_mem μ B hB
  refine ⟨π,hπ,compressionBudget 0 n (2*R) C,compressionBudget_ne_top 0 n _ hC,hgeo,?_,
    (fun t => (hall t).1),?_,?_,?_⟩
  · rw [hend.1,hend.2]
    exact hopt
  · filter_upwards [hstart,hfinish,hpaths] with γ ha hb hg
    exact ⟨ha,hb,hg.2⟩
  · rwa [hend.1]
  · rwa [hend.2]

end RegularPointCoordinates

end

end OAI
