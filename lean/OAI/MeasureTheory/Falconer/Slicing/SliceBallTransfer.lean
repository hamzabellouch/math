import OAI.MeasureTheory.Falconer.Slicing.SliceGeometry

namespace OAI

/-! # Ball estimates for the actual point and direction slice coordinates -/

namespace Falconer
open Set Metric MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem pointSlice_projection_ball_bound (V : Submodule ℝ (Space d))
    (μ : Measure (Space d)) (z : Space d) {δ K s : ℝ} (hδ : 0 ≤ δ)
    (hsupport : ∀ᵐ x ∂μ, x ∈ pointSliceBand V z δ)
    (hball : ∀ x : Space d, ∀ r : ℝ, δ ≤ r →
      μ (ball x r) ≤ ENNReal.ofReal (K*r^s))
    (a : Space d) {r : ℝ} (hr : δ ≤ r) :
    (Measure.map V.starProjection μ) (ball a r) ≤ ENNReal.ofReal (K*(2*r)^s) := by
  rw [Measure.map_apply V.starProjection.continuous.measurable measurableSet_ball]
  apply (measure_mono_ae ?_).trans (hball (a+z) (2*r) (by linarith))
  filter_upwards [hsupport] with x hx
  intro hxa
  have ha : ‖V.starProjection x-a‖ < r := by
    simpa only [mem_preimage,mem_ball,dist_eq_norm] using hxa
  have he : x-(a+z) = (V.starProjection x-a)+(Vᗮ.starProjection x-z) := by
    rw [Submodule.starProjection_orthogonal_val]
    abel
  change ‖x-(a+z)‖ < 2*r
  rw [he]
  have hb : ‖Vᗮ.starProjection x-z‖ ≤ δ := hx
  exact (norm_add_le _ _).trans_lt (by linarith)

theorem normalizedSlice_projection_ball_bound (V : Submodule ℝ (Space d))
    (ν : Measure (Sphere d)) {δ K s : ℝ} (hδ : δ < 1)
    (hsupport : ∀ᵐ w ∂ν, w ∈ directionSliceBand V δ)
    (hball : ∀ a : Space d, ∀ r : ℝ, δ ≤ r →
      ν {w : Sphere d | dist (w:Space d) a < r} ≤ ENNReal.ofReal (K*r^s))
    (a : Space d) {r : ℝ} (hr : δ ≤ r) (hr₀ : 0 ≤ r) :
    (Measure.map (fun w : Sphere d => normalize (V.starProjection (w:Space d))) ν) (ball a r) ≤
      ENNReal.ofReal (K*(3*r)^s) := by
  have hm : Measurable (fun w : Sphere d => normalize (V.starProjection (w:Space d))) := by
    unfold NormedSpace.normalize
    fun_prop
  rw [Measure.map_apply hm measurableSet_ball]
  apply (measure_mono_ae ?_).trans (hball a (3*r) (by linarith))
  filter_upwards [hsupport] with w hw
  intro hwa
  have hh := directionSliceBand_normalize_error V hδ hw
  have ha : ‖normalize (V.starProjection (w:Space d))-a‖ < r := by
    simpa only [mem_preimage,mem_ball,dist_eq_norm] using hwa
  change ‖(w:Space d)-a‖ < 3*r
  have he := norm_sub_le_norm_sub_add_norm_sub (w:Space d)
    (normalize (V.starProjection (w:Space d))) a
  have hh' : ‖(w:Space d)-normalize (V.starProjection (w:Space d))‖ ≤ 2*δ := by
    simpa only [norm_sub_rev] using hh
  linarith

end Falconer

end OAI
