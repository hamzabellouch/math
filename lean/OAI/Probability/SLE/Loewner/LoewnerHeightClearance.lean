import OAI.Probability.SLE.Gauge.RibbonSurvival
import OAI.Probability.SLE.Geometry.NormalizedMarkedState
import OAI.Probability.SLE.Geometry.HyperbolicGuideCompactness

namespace OAI

/-! A hypothetical upper bound on the trace height gives a physical
clearance ball and hence a lower bound on the inverse derivative. -/
noncomputable section
open Set Filter Metric
open scoped Topology NNReal

namespace SLEExactGauge

lemma survives_above_trace_height
    (γ : ℝ≥0 → ℂ) (T : ℝ≥0) (H : ℝ)
    (hγ : ∀ t ∈ Icc 0 T, (γ t).im ≤ H) {z : ℂ}
    (hz : 0 < z.im) (hH : H < z.im) : z ∈ survivingDomain γ T := by
  have hf : range (upwardRay z) ⊆ upperHalfPlane \ (γ '' Icc 0 T) := by
    rintro w ⟨s,rfl⟩
    have hi : (upwardRay z s).im = z.im+s := by simp [upwardRay]
    refine ⟨?_,?_⟩
    · change 0 < (upwardRay z s).im
      rw [hi]
      exact add_pos_of_pos_of_nonneg hz s.coe_nonneg
    · rintro ⟨t,ht,he⟩
      have hh := hγ t ht
      rw [he,hi] at hh
      linarith [s.coe_nonneg]
  have hh := survives_of_unbounded_free_curve γ T (upwardRay z)
    (upwardRay_continuous z) hf (upwardRay_unbounded z) (mem_range_self 0)
  simpa [upwardRay] using hh

lemma IsCapacityTwoWitness.inverse_clearance_bound
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) {w : ℂ}
    (hw : w ∈ upperHalfPlane) {r : ℝ} (hr : 0 < r)
    (hball : ball (F T w) r ⊆ survivingDomain γ T) :
    r ≤ (128*Real.pi)*w.im*‖deriv (F T) w‖ := by
  have hD := h.2.2.2.2.2.2.1 T hw
  have hid := h.inverse_derivative_identity T (F T w) hD
  rw [h.2.2.2.2.2.2.2.2.1 T w hw] at hid
  have hnorm := congrArg norm hid
  rw [norm_mul,norm_one] at hnorm
  have hi : InjOn (G T) (survivingDomain γ T) := by
    intro z hz v hv he
    rw [← h.2.2.2.2.2.2.2.1 T z hz,he,h.2.2.2.2.2.2.2.1 T v hv]
  have hd := HyperbolicGuideCompactness.inverse_chart_derivative_bound hr
    ((h.2.2.2.1 T).mono hball) (hi.mono hball)
    (fun z hz => h.2.2.2.2.2.1 T (hball hz))
  rw [h.2.2.2.2.2.2.2.2.1 T w hw] at hd
  have hm := mul_le_mul_of_nonneg_right hd (norm_nonneg (deriv (F T) w))
  have hone : 1 ≤ (128*Real.pi/r)*w.im*‖deriv (F T) w‖ := by
    simpa only [mul_comm ‖deriv (G T) (F T w)‖,hnorm,mul_assoc] using hm
  calc
    r = 1*r := by ring
    _ ≤ ((128*Real.pi/r)*w.im*‖deriv (F T) w‖)*r :=
      mul_le_mul_of_nonneg_right hone hr.le
    _ = (128*Real.pi)*w.im*‖deriv (F T) w‖ := by field_simp

end SLEExactGauge

end

end OAI
