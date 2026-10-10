import OAI.Probability.SLE.Loewner.SlitUniformInverseBound
import OAI.Probability.SLE.Loewner.InverseDirichletEnergy

namespace OAI

/-! A common finite Dirichlet-energy bound for the whole initial inverse
family on a fixed upper half-disk. -/
noncomputable section
open Set Filter Function Complex Metric MeasureTheory
open scoped Topology ENNReal

namespace SLEExactGauge

theorem initialInverse_dirichlet_bound (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {R : ℝ} (hR : 0<R) (hp : ∀ t : unitInterval, ‖p t‖<R)
    (s : unitInterval) (A : ℝ) :
    (∫⁻ z in upperHalfPlane ∩ ball (0:ℂ) A,
      ENNReal.ofReal (‖deriv (initialInverseChart p hi h0 hH s) z‖^2))≤
        volume (closedBall (0:ℂ) (A+3*R)) := by
  let F := initialInverseChart p hi h0 hH s
  let S := upperHalfPlane ∩ ball (0:ℂ) A
  have hS : MeasurableSet S := isOpen_upperHalfPlane.measurableSet.inter measurableSet_ball
  have hd (z : ℂ) (hz : z∈S) : HasDerivAt F (deriv F z) z :=
    ((initialInverseChart_differentiableOn p hi h0 hH s).differentiableAt
      (isOpen_upperHalfPlane.mem_nhds hz.1)).hasDerivAt
  have hinj : InjOn F S := by
    intro z hz w hw he
    have hz' := initialForward_inverse p hi h0 hH s hz.1
    have hw' := initialForward_inverse p hi h0 hH s hw.1
    change initialForwardChart p hi h0 hH s (F z)=z at hz'
    change initialForwardChart p hi h0 hH s (F w)=w at hw'
    rw [he,hw'] at hz'
    exact hz'.symm
  have he : (∫⁻ z in S, ENNReal.ofReal (‖deriv F z‖^2))=volume (F '' S) := by
    have hh := lintegral_abs_det_fderiv_eq_addHaar_image volume hS
      (fun z hz => ((hd z hz).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt) hinj
    simpa only [complex_derivative_real_det,abs_pow,abs_norm] using hh
  change (∫⁻ z in S, ENNReal.ofReal (‖deriv F z‖^2))≤_
  rw [he]
  apply measure_mono
  rintro _ ⟨z,hz,rfl⟩
  rw [mem_closedBall_zero_iff]
  have hb := initialInverse_uniform_bound p hi h0 hH hR hp s hz.1
  have hzA : ‖z‖<A := mem_ball_zero_iff.mp hz.2
  exact hb.trans (by linarith)

end SLEExactGauge

end

end OAI
