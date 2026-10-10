import OAI.Probability.SLE.Loewner.InverseBoundaryBound
import OAI.Probability.SLE.Gauge.ConformalSausageTransfer

namespace OAI

/-! Finite local Dirichlet energy for the inverse Loewner chart follows
from injectivity, the area formula and hydrodynamic boundedness. -/
noncomputable section
open Set Filter Metric Function MeasureTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

lemma IsCapacityTwoWitness.inverse_local_dirichlet_finite
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (t : ℝ≥0) (x : ℂ) (R : ℝ) :
    (∫⁻ z in upperHalfPlane ∩ ball x R, ENNReal.ofReal (‖deriv (F t) z‖^2))<∞ := by
  let S := upperHalfPlane ∩ ball x R
  have hS : MeasurableSet S := isOpen_upperHalfPlane.measurableSet.inter measurableSet_ball
  have hder (z : ℂ) (hz : z∈S) : HasDerivAt (F t) (deriv (F t) z) z :=
    ((hw.2.2.2.2.1 t).differentiableAt (isOpen_upperHalfPlane.mem_nhds hz.1)).hasDerivAt
  have hinj : InjOn (F t) S := by
    intro z hz w hw' he
    have h1 := hw.2.2.2.2.2.2.2.2.1 t z hz.1
    have h2 := hw.2.2.2.2.2.2.2.2.1 t w hw'.1
    rw [he,h2] at h1
    exact h1.symm
  have harea : (∫⁻ z in S, ENNReal.ofReal (‖deriv (F t) z‖^2)) = volume (F t '' S) := by
    have he := lintegral_abs_det_fderiv_eq_addHaar_image volume hS
      (fun z hz => ((hder z hz).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt) hinj
    simpa only [complex_derivative_real_det,abs_pow,abs_norm] using he
  obtain ⟨M,hM⟩ := hw.inverse_bounded_over_ball t (R+‖x‖)
  have himage : F t '' S ⊆ closedBall (0:ℂ) M := by
    rintro _ ⟨z,hz,rfl⟩
    rw [mem_closedBall,dist_zero_right]
    apply hM z hz.1
    have hnear : ‖z-x‖<R := by simpa only [mem_ball,dist_eq_norm] using hz.2
    have := norm_le_norm_sub_add z x
    linarith
  rw [harea]
  exact (measure_mono himage).trans_lt (isCompact_closedBall (0:ℂ) M).measure_lt_top

end SLEExactGauge

end

end OAI
