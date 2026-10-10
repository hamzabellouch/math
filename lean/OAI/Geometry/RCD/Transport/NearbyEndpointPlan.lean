import OAI.Geometry.RCD.Transport.NearbySegment

namespace OAI

/-! # Actual nearby-endpoint plans with an explicit normalized compression bound -/

open Set Filter MeasureTheory Metric
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.nearby_endpoint_plan {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2≤n) (hK : K≤0)
    {p x y : X} {R ρ : ℝ} (hR : 0<R) (hρ : 0<ρ) (hρR : ρ≤R/2)
    (hx : dist x p≤R/2) (hy : dist y p≤R/2) (hcurv : -1≤K*(4*R)^2) :
    ∃ π : Measure C(Time,X), IsProbabilityMeasure π ∧
      (∀ᵐ γ ∂π, IsGeodesic γ) ∧
      IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
        (π.map (fun γ => (γ 0,γ 1))) ∧
      (∀ t : Time, π.map (fun γ => γ t)≤
        ENNReal.ofReal (segmentCost n*R^n/((hausdorff n X).real (ball p R)*ρ^n)) • hausdorff n X) ∧
      ∀ᵐ γ ∂π, dist (γ 0) x<ρ ∧ dist (γ 1) y<ρ ∧ ∀ t : Time, dist (γ t) p≤3*R := by
  let μ := hausdorff n X
  have hsub (z : X) (hz : dist z p≤R/2) : ball z ρ⊆closedBall p R := by
    intro w hw
    have ht := dist_triangle w z p
    have hwz : dist w z<ρ := hw
    change dist w p≤R
    linarith
  let A := ball x ρ
  let B := ball y ρ
  let C : ℝ≥0∞ := max (μ A)⁻¹ (μ B)⁻¹
  have hA0 : μ A≠0 := (hX.fullSupport x ρ hρ).ne'
  have hB0 : μ B≠0 := (hX.fullSupport y ρ hρ).ne'
  have hAt : μ A≠∞ := (hX.finiteOnBounded _ isBounded_ball).ne
  have hBt : μ B≠∞ := (hX.finiteOnBounded _ isBounded_ball).ne
  have hC : C≠∞ := max_ne_top (ENNReal.inv_ne_top.mpr hA0) (ENNReal.inv_ne_top.mpr hB0)
  let := uniformOn_probability μ A hA0 hAt
  let := uniformOn_probability μ B hB0 hBt
  have hbA : ∀ᵐ z ∂uniformOn μ A, dist z p≤R :=
    (uniformOn_ae_mem μ A measurableSet_ball).mono (fun _ hz => hsub x hx hz)
  have hbB : ∀ᵐ z ∂uniformOn μ B, dist z p≤R :=
    (uniformOn_ae_mem μ B measurableSet_ball).mono (fun _ hz => hsub y hy hz)
  obtain ⟨π,hπ,hgeo,hopt,_hi,hall⟩ := hX.exists_bounded_entropy_plan K n hn
    (uniformOn μ A) (uniformOn μ B) hC (uniformOn_le_scaled μ A (le_max_left _ _))
    (uniformOn_le_scaled μ B (le_max_right _ _)) p hR.le hbA hbB
  let := hπ
  have hend := optimalPlan_endpoints (uniformOn μ A) (uniformOn μ B) π hopt
  have hpaths := optimal_geodesic_plan_bounded (uniformOn μ A) (uniformOn μ B)
    π hgeo hopt p hR.le hbA hbB
  have hstart : ∀ᵐ γ ∂π, γ 0∈A := by
    apply ae_of_ae_map (measurable_path_eval 0).aemeasurable
    rw [hend.1]
    exact uniformOn_ae_mem μ A measurableSet_ball
  have hfinish : ∀ᵐ γ ∂π, γ 1∈B := by
    apply ae_of_ae_map (measurable_path_eval 1).aemeasurable
    rw [hend.2]
    exact uniformOn_ae_mem μ B measurableSet_ball
  have hCb : (compressionBudget K n (2*R) C).toReal≤
      segmentCost n*R^n/(μ.real (ball p R)*ρ^n) := by
    have he := compressionBudget_le_of_rescaled_curvature hn hK hcurv C
    have hc := hX.endpoint_ball_compression_bound (p:=p) (x:=x) (y:=y) hn hR hρ (by linarith)
      (by linarith) (by linarith) (by nlinarith : -1≤K*(2*R)^2)
    exact he.trans (by
      have hh := mul_le_mul_of_nonneg_left hc (Real.exp_pos (n:ℝ)).le
      convert hh using 1
      dsimp only [segmentCost]
      ring)
  have hC' : compressionBudget K n (2*R) C≤
      ENNReal.ofReal (segmentCost n*R^n/(μ.real (ball p R)*ρ^n)) := by
    rw [← ENNReal.ofReal_toReal (compressionBudget_ne_top K n (2*R) hC)]
    exact ENNReal.ofReal_le_ofReal hCb
  refine ⟨π,hπ,hgeo,?_,?_,?_⟩
  · rwa [hend.1,hend.2]
  · intro t
    apply (hall t).1.trans
    apply Measure.le_iff.mpr
    intro U _hU
    simpa only [Measure.smul_apply,smul_eq_mul] using mul_le_mul' hC' le_rfl
  · filter_upwards [hstart,hfinish,hpaths] with γ ha hb hp
    exact ⟨ha,hb,hp.2⟩

end RegularPointCoordinates

end

end OAI
