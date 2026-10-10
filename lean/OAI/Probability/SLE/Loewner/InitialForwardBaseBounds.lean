import OAI.Probability.SLE.Loewner.InitialForwardChart
import OAI.Probability.SLE.Loewner.SlitChartVerticalBounds

namespace OAI

/-! Uniform interior control at a single exterior base point for every initial chart. -/
noncomputable section
open Set Filter Function Complex Metric
open scoped Topology

namespace SLEExactGauge

lemma initialForwardChart_base_bounds (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane)
    {R : ℝ} (hR : 0<R) (hp : ∀ u : unitInterval, ‖p u‖≤R) (t : unitInterval) :
    3*R/2≤(initialForwardChart p hi h0 hH t (((2*R:ℝ):ℂ)*I)).im ∧
      ‖initialForwardChart p hi h0 hH t (((2*R:ℝ):ℂ)*I)‖≤3*R := by
  by_cases ht : t=0
  · simp only [ht,initialForwardChart_zero,id_eq]
    have hn : ‖((2*R:ℝ):ℂ)*I‖=2*R := by
      simp [abs_of_pos hR]
    rw [hn]
    simp only [mul_im,ofReal_re,I_im,mul_one,ofReal_im,I_re,mul_zero,add_zero]
    constructor <;> linarith
  · rw [initialForwardChart,dite_eq_right ht]
    apply (initialSlitChart p hi h0 hH t ht).vertical_base_bounds hR
    intro u
    exact hp (t*u)

lemma initialForward_base_mem_domain (p : C(unitInterval,ℂ)) {R : ℝ}
    (hR : 0<R) (hp : ∀ u : unitInterval, ‖p u‖≤R) :
    (((2*R:ℝ):ℂ)*I)∈upperHalfPlane \ range p := by
  have hn : ‖((2*R:ℝ):ℂ)*I‖=2*R := by
    simp [abs_of_pos hR]
  refine ⟨?_,?_⟩
  · change 0<(((2*R:ℝ):ℂ)*I).im
    simpa using mul_pos (by norm_num : (0:ℝ)<2) hR
  · rintro ⟨u,hu⟩
    have hh := hp u
    rw [hu,hn] at hh
    linarith

end SLEExactGauge

end

end OAI
