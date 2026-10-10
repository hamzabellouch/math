import OAI.Probability.SLE.Geometry.CircleRadialFlux
import OAI.Probability.SLE.Geometry.ConformalLaplacian

namespace OAI

/-! Complex-coordinate expression for the radial flux of a squared
holomorphic norm. -/
noncomputable section
open Set Filter Metric Function Complex MeasureTheory InnerProductSpace Real
open scoped Topology Laplacian ComplexConjugate

namespace SLEExactGauge

lemma holomorphic_radial_flux {f : ℂ → ℂ} {r θ : ℝ}
    (hf : AnalyticAt ℂ f (polarPoint r θ)) :
    radialLaplacianFlux (fun z => ‖f z‖^2) (r,θ)=
      2*(polarPoint r θ*deriv f (polarPoint r θ)*conj (f (polarPoint r θ))).re := by
  have hd : HasDerivAt (fun s => f (polarPoint s θ))
      (circleMap 0 1 θ*deriv f (polarPoint r θ)) r := by
    have hh := (hf.differentiableAt.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt r
      (polarPoint_radial_hasDeriv r θ)
    rwa [complex_fderiv_apply hf.differentiableAt] at hh
  have hu : ContDiffAt ℝ 2 (fun z => ‖f z‖^2) (polarPoint r θ) :=
    hf.contDiffAt.restrict_scalars ℝ |>.norm_sq ℝ
  have he := (radial_partial_hasDeriv hu).unique hd.norm_sq
  rw [radialLaplacianFlux,he,Complex.inner]
  have hmul : (polarPoint r θ*deriv f (polarPoint r θ)*conj (f (polarPoint r θ))).re=
      r*(circleMap 0 1 θ*deriv f (polarPoint r θ)*conj (f (polarPoint r θ))).re := by
    simp only [polarPoint,smul_mul_assoc,Complex.smul_re,smul_eq_mul]
  rw [hmul]
  ring

end SLEExactGauge

end

end OAI
