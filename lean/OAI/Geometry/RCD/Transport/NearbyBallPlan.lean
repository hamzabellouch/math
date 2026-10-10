import OAI.Geometry.RCD.Harmonic.DefectSegment

namespace OAI

/-! # Compressed geodesic plans between two small endpoint balls -/

open Set Filter Metric MeasureTheory
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.nearby_ball_plan {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) (x y : X) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ π : Measure C(Time,X), IsProbabilityMeasure π ∧
      ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      (∀ᵐ γ ∂π, IsGeodesic γ) ∧
      MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π ∧
      (∀ t : Time, π.map (fun γ => γ t) ≤ C • hausdorff n X) ∧
      (∀ᵐ γ ∂π, dist (γ 0) x < ρ ∧ dist (γ 1) y < ρ ∧
        ∀ t : Time, dist (γ t) x ≤ 3*(dist x y+ρ)) := by
  let := hX.separable
  let μ := hausdorff n X
  let A := ball x ρ
  let B := ball y ρ
  let R := dist x y+ρ
  have hR : 0 < R := add_pos_of_nonneg_of_pos dist_nonneg hρ
  have hA0 : μ A ≠ 0 := (hX.fullSupport x ρ hρ).ne'
  have hB0 : μ B ≠ 0 := (hX.fullSupport y ρ hρ).ne'
  have hAt : μ A ≠ ∞ := (hX.finiteOnBounded A isBounded_ball).ne
  have hBt : μ B ≠ ∞ := (hX.finiteOnBounded B isBounded_ball).ne
  let C := max (μ A)⁻¹ (μ B)⁻¹
  have hC : C ≠ ∞ := max_ne_top (ENNReal.inv_ne_top.mpr hA0) (ENNReal.inv_ne_top.mpr hB0)
  let := uniformOn_probability μ A hA0 hAt
  let := uniformOn_probability μ B hB0 hBt
  have hbA : ∀ᵐ w ∂uniformOn μ A, dist w x ≤ R := by
    filter_upwards [uniformOn_ae_mem μ A measurableSet_ball] with w hw
    change dist w x < ρ at hw
    dsimp only [R]
    linarith [dist_nonneg (x := x) (y := y)]
  have hbB : ∀ᵐ w ∂uniformOn μ B, dist w x ≤ R := by
    filter_upwards [uniformOn_ae_mem μ B measurableSet_ball] with w hw
    change dist w y < ρ at hw
    have hh := dist_triangle w y x
    rw [dist_comm y x] at hh
    dsimp only [R]
    linarith
  obtain ⟨π,hπ,hgeo,hopt,hi,hcomp⟩ := hX.exists_bounded_entropy_plan K n hn
    (uniformOn μ A) (uniformOn μ B) hC (uniformOn_le_scaled μ A (le_max_left _ _))
    (uniformOn_le_scaled μ B (le_max_right _ _)) x hR.le hbA hbB
  let := hπ
  obtain ⟨h0,h1⟩ := optimalPlan_endpoints (uniformOn μ A) (uniformOn μ B) π hopt
  have hp := optimal_geodesic_plan_bounded (uniformOn μ A) (uniformOn μ B)
    π hgeo hopt x hR.le hbA hbB
  have hstart : ∀ᵐ γ ∂π, γ 0 ∈ A := by
    apply ae_of_ae_map (measurable_path_eval 0).aemeasurable
    rw [h0]
    exact uniformOn_ae_mem μ A measurableSet_ball
  have hfinish : ∀ᵐ γ ∂π, γ 1 ∈ B := by
    apply ae_of_ae_map (measurable_path_eval 1).aemeasurable
    rw [h1]
    exact uniformOn_ae_mem μ B measurableSet_ball
  refine ⟨π,hπ,compressionBudget K n (2*R) C,compressionBudget_ne_top K n _ hC,hgeo,?_,
    fun t => (hcomp t).1,?_⟩
  · exact (memLp_two_iff_integrable_sq
      ((measurable_path_eval 0).dist (measurable_path_eval 1)).aestronglyMeasurable).mpr hi
  · filter_upwards [hstart,hfinish,hp] with γ hγ0 hγ1 hγ
    exact ⟨hγ0,hγ1,hγ.2⟩

end RegularPointCoordinates

end

end OAI
