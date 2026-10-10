import OAI.Probability.SLE.LoewnerCharts

namespace OAI

/-!
A fixed interior ball separated from the moving tip images in the guide
compactness argument. Only local uniform convergence and continuity of
the limit are used.
-/

noncomputable section
open Set Filter Metric
open scoped Topology

namespace SLEExactGauge

/-- A non-tip interior value of the limiting map supplies a fixed closed
ball whose images stay uniformly away from the moving tip values. -/
theorem exists_interior_ball_eventually_separated
    (Fₙ : ℕ → ℂ → ℂ) (F : ℂ → ℂ) (aₙ : ℕ → ℂ) (a z₀ : ℂ)
    (hconv : TendstoLocallyUniformlyOn Fₙ F atTop upperHalfPlane)
    (ha : Tendsto aₙ atTop (𝓝 a)) (hF : ContinuousOn F upperHalfPlane)
    (hz₀ : z₀ ∈ upperHalfPlane) (hne : F z₀ ≠ a) :
    ∃ ρ r₀ : ℝ, 0 < ρ ∧ 0 < r₀ ∧ closedBall z₀ ρ ⊆ upperHalfPlane ∧
      ∀ᶠ n in atTop, ∀ z ∈ closedBall z₀ ρ, r₀ ≤ ‖Fₙ n z - aₙ n‖ := by
  let D : ℝ := ‖F z₀ - a‖
  have hD : 0 < D := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hcont : ContinuousAt (fun z => ‖F z - a‖) z₀ :=
    ((hF.continuousAt (isOpen_upperHalfPlane.mem_nhds hz₀)).sub_const a).norm
  have hsep : {z : ℂ | D / 2 < ‖F z - a‖} ∈ 𝓝 z₀ :=
    hcont.preimage_mem_nhds (Ioi_mem_nhds (by dsimp only [D] at hD ⊢; linarith))
  obtain ⟨ρ, hρ, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (inter_mem (isOpen_upperHalfPlane.mem_nhds hz₀) hsep)
  have hballH : closedBall z₀ ρ ⊆ upperHalfPlane := fun z hz => (hball hz).1
  have hu : TendstoUniformlyOn Fₙ F atTop (closedBall z₀ ρ) :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
      (isCompact_closedBall z₀ ρ)).mp (hconv.mono hballH)
  have herror : ∀ᶠ n in atTop, ∀ z ∈ closedBall z₀ ρ,
      dist (F z) (Fₙ n z) < D / 8 :=
    hu _ (Metric.dist_mem_uniformity (by positivity : 0 < D / 8))
  have haerror : ∀ᶠ n in atTop, dist (aₙ n) a < D / 8 :=
    Metric.tendsto_nhds.mp ha (D / 8) (by positivity)
  refine ⟨ρ, D / 4, hρ, by positivity, hballH, ?_⟩
  filter_upwards [herror, haerror] with n hn han
  intro z hz
  have hseparated : D / 2 < dist (F z) a := by
    rw [dist_eq_norm]
    exact (hball hz).2
  have htriangle : dist (F z) a ≤
      dist (F z) (Fₙ n z) + dist (Fₙ n z) (aₙ n) + dist (aₙ n) a := by
    calc
      _ ≤ dist (F z) (Fₙ n z) + dist (Fₙ n z) a := dist_triangle _ _ _
      _ ≤ dist (F z) (Fₙ n z) + (dist (Fₙ n z) (aₙ n) + dist (aₙ n) a) :=
        by linarith [dist_triangle (Fₙ n z) (aₙ n) a]
      _ = _ := by ring
  have he := hn z hz
  rw [← dist_eq_norm]
  linarith

end SLEExactGauge

end

end OAI
