import OAI.Geometry.RCD.Transport.CompressedSegmentNullSet
import OAI.Geometry.RCD.Transport.TransportLevelBound

namespace OAI

/-! # An actual geodesic with controlled local defect

Positive endpoint sets are connected by the already constructed RCD
bounded-compression plan. First-moment selection retains its endpoints,
geodesicity, and whole-path containment. No segment or splitting input is
assumed.
-/

open Set Filter Metric MeasureTheory
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.exists_defect_segment {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n)
    (p : X) {R : ℝ} (hR : 0 < R) {A B : Set X}
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hA0 : hausdorff n X A ≠ 0) (hB0 : hausdorff n X B ≠ 0)
    (hsA : A ⊆ closedBall p R) (hsB : B ⊆ closedBall p R)
    {F : X → ℝ} (hF : IntegrableOn F (ball p (8*R)) (hausdorff n X))
    (hFpos : ∀ᵐ x ∂(hausdorff n X).restrict (ball p (8*R)), 0 ≤ F x)
    {P : X → Prop} (hP : ∀ᵐ x ∂(hausdorff n X).restrict (ball p (8*R)), P x) :
    ∃ γ : C(Time,X), IsGeodesic γ ∧ γ 0 ∈ A ∧ γ 1 ∈ B ∧
      (∀ t : Time, dist (γ t) p ≤ 3*R) ∧
      (∀ᵐ t ∂volume.restrict (Icc (0:ℝ) 1), P (geodesicExtension γ t)) ∧
      IntegrableOn (fun t => F (geodesicExtension γ t)) (Icc (0:ℝ) 1) ∧
      (∫ t in Icc (0:ℝ) 1, F (geodesicExtension γ t)) ≤
        (compressionBudget K n (2*R)
          (max (hausdorff n X A)⁻¹ (hausdorff n X B)⁻¹)).toReal *
          ∫ x in ball p (8*R), F x ∂hausdorff n X := by
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
  obtain ⟨π,hπ,hgeo,hopt,_hi,hall⟩ := hX.exists_bounded_entropy_plan K n hn
    (uniformOn μ A) (uniformOn μ B) hC (uniformOn_le_scaled μ A (le_max_left _ _))
    (uniformOn_le_scaled μ B (le_max_right _ _)) p hR.le hbA hbB
  let := hπ
  have hend := optimalPlan_endpoints (uniformOn μ A) (uniformOn μ B) π hopt
  have hpaths := optimal_geodesic_plan_bounded (uniformOn μ A) (uniformOn μ B)
    π hgeo hopt p hR.le hbA hbB
  have hstay (t : Time) : ∀ᵐ x ∂π.map (fun γ => γ t), x ∈ ball p (8*R) := by
    apply (ae_map_iff (measurable_path_eval t).aemeasurable measurableSet_ball).mpr
    filter_upwards [hpaths] with γ hγ
    linarith [hγ.2 t]
  have hstart : ∀ᵐ γ ∂π, γ 0 ∈ A := by
    apply ae_of_ae_map (measurable_path_eval 0).aemeasurable
    rw [hend.1]
    exact uniformOn_ae_mem μ A hA
  have hfinish : ∀ᵐ γ ∂π, γ 1 ∈ B := by
    apply ae_of_ae_map (measurable_path_eval 1).aemeasurable
    rw [hend.2]
    exact uniformOn_ae_mem μ B hB
  have hgood : ∀ᵐ γ ∂π, IsGeodesic γ ∧ γ 0 ∈ A ∧ γ 1 ∈ B ∧
      (∀ t : Time, dist (γ t) p ≤ 3*R) ∧
      (∀ᵐ t ∂volume.restrict (Icc (0:ℝ) 1), P (geodesicExtension γ t)) := by
    have hPa := compressed_segment_ae μ π (fun t => (hall t).1) hstay hP
    filter_upwards [hpaths,hstart,hfinish,hPa] with γ hγ ha hb hp
    exact ⟨hγ.1,ha,hb,hγ.2,hp⟩
  obtain ⟨γ,hγ,hinner,hbound⟩ := exists_compressed_segment μ π
    (compressionBudget_ne_top K n (2*R) hC) (fun t => (hall t).1) hstay hF hFpos hgood
  exact ⟨γ,hγ.1,hγ.2.1,hγ.2.2.1,hγ.2.2.2.1,hγ.2.2.2.2,hinner,hbound⟩

end RegularPointCoordinates

end

end OAI
