import OAI.Probability.SLE.Loewner.LoewnerVerticalLimit

namespace OAI

/-! The derivative of a holomorphic inverse limit is determined by its
explicit values on the positive imaginary axis. -/
noncomputable section
open Set Filter Complex
open scoped Topology NNReal

namespace SLEExactGauge

lemma vertical_axis_derivative (f : ℂ → ℂ) (T : ℝ≥0)
    (hf : DifferentiableOn ℂ f upperHalfPlane)
    (haxis : ∀ y : ℝ, 0 < y → f ((y:ℂ)*I)=verticalReversePath y T)
    {y : ℝ} (hy : 0 < y) :
    deriv f ((y:ℂ)*I) = ((y/Real.sqrt (y^2+4*T) : ℝ) : ℂ) := by
  have hp : 0 < y^2+4*(T:ℝ) := by positivity
  have hd := (((hasDerivAt_id y).pow 2).add_const (4*(T:ℝ))).sqrt hp.ne'
  have hreal : HasDerivAt (fun s : ℝ => verticalReversePath s T)
      (((y/Real.sqrt (y^2+4*T) : ℝ) : ℂ)*I) y := by
    convert! hd.ofReal_comp.mul_const I using 1
    congr 2
    simp only [Pi.pow_apply,id_eq,mul_one]
    ring
  have hhol := hf.differentiableAt (isOpen_upperHalfPlane.mem_nhds
    (show (y:ℂ)*I ∈ upperHalfPlane by simpa [upperHalfPlane] using hy))
  have harg : HasDerivAt (fun s : ℝ => (s:ℂ)*I) I y := by
    simpa using (hasDerivAt_id y).ofReal_comp.mul_const I
  have hc := (hhol.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt y harg
  have hval : (fderiv ℝ f ((y:ℂ)*I)) I = I*deriv f ((y:ℂ)*I) := by
    rw [hhol.fderiv_restrictScalars (𝕜 := ℝ)]
    change (fderiv ℂ f ((y:ℂ)*I)) I = _
    rw [fderiv_eq_smul_deriv,smul_eq_mul]
  rw [hval] at hc
  have he : (fun s : ℝ => f ((s:ℂ)*I)) =ᶠ[𝓝 y]
      (fun s : ℝ => verticalReversePath s T) := by
    filter_upwards [Ioi_mem_nhds hy] with s hs
    exact haxis s hs
  have heq := (hc.congr_of_eventuallyEq he.symm).unique hreal
  rw [mul_comm I] at heq
  exact mul_right_cancel₀ I_ne_zero heq

end SLEExactGauge

end

end OAI
