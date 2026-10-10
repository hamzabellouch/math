import OAI.Probability.SLE.Loewner.InitialInverseEnergyIntegral
import OAI.Probability.SLE.Loewner.VerticalIntervalEnergy

namespace OAI

/-! Exact derivatives on vertical lines in the upper half-plane. -/
noncomputable section
open Set Filter Function Complex MeasureTheory
open scoped Topology

namespace SLEExactGauge

lemma holomorphic_vertical_hasDerivAt {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F upperHalfPlane) (x : ℝ) {y : ℝ} (hy : 0<y) :
    HasDerivAt (fun t : ℝ => F ((x:ℂ)+(t:ℂ)*Complex.I))
      (Complex.I*deriv F ((x:ℂ)+(y:ℂ)*Complex.I)) y := by
  have hp : (x:ℂ)+(y:ℂ)*Complex.I∈upperHalfPlane := by
    change 0<((x:ℂ)+(y:ℂ)*Complex.I).im
    simpa only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,add_zero,zero_add] using hy
  have hc := ((Complex.ofRealCLM.hasDerivAt (x := y)).mul_const Complex.I).const_add (x:ℂ)
  have hd := ((hF.differentiableAt (isOpen_upperHalfPlane.mem_nhds hp)).hasDerivAt.hasFDerivAt).restrictScalars ℝ
  have hh := hd.comp_hasDerivAt y hc
  simpa only [ContinuousLinearMap.coe_restrictScalars',ContinuousLinearMap.toSpanSingleton_apply,
    Complex.ofRealCLM_apply,ofReal_one,one_mul,mul_one,smul_eq_mul,Function.comp_def,mul_comm] using hh

lemma holomorphic_vertical_deriv_norm {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F upperHalfPlane) (x : ℝ) {y : ℝ} (hy : 0<y) :
    ‖deriv (fun t : ℝ => F ((x:ℂ)+(t:ℂ)*Complex.I)) y‖=
      ‖deriv F ((x:ℂ)+(y:ℂ)*Complex.I)‖ := by
  rw [(holomorphic_vertical_hasDerivAt hF x hy).deriv,norm_mul,norm_I,one_mul]

end SLEExactGauge

end

end OAI
