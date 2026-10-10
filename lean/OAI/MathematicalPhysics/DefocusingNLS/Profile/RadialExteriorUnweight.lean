import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorNonlinearTail

namespace OAI

/-! Removing the exponential weight from the nonlinear exterior error equation. -/

namespace DefocusingNLS

noncomputable def radialExteriorUnweight (κ : ℝ) (v : ℝ → ℂ × ℂ) (t : ℝ) : ℂ × ℂ :=
  Real.exp (-κ*t) • v t

theorem radialExteriorUnweight_hasDerivAt (κ t : ℝ) (ν : ℂ) (N : ℂ → ℂ)
    (f : ℝ → ℂ) (r : ℝ → ℂ × ℂ) (v : ℝ → ℂ × ℂ)
    (hv : HasDerivAt v
      (κ • v t+(0,-Complex.I*(Real.exp (2*t)/2 : ℝ)*(v t).2)+
        radialExteriorErrorMatrix ν (v t)+
        (0,radialExteriorWeightedIncrement κ N f t (v t).1)+r t) t) :
    HasDerivAt (radialExteriorUnweight κ v)
      ((0,-Complex.I*(Real.exp (2*t)/2 : ℝ)*(radialExteriorUnweight κ v t).2)+
        radialExteriorErrorMatrix ν (radialExteriorUnweight κ v t)+
        (0,N (f t+(radialExteriorUnweight κ v t).1)-N (f t))+
        Real.exp (-κ*t) • r t) t := by
  have he : HasDerivAt (fun s : ℝ => Real.exp (-κ*s)) (-κ*Real.exp (-κ*t)) t := by
    convert ((hasDerivAt_id t).const_mul (-κ)).exp using 1 <;> simp [mul_comm]
  have h := he.smul hv
  apply h.congr_deriv
  have hc : Complex.exp (-((κ : ℂ)*(t : ℂ)))*Complex.exp ((κ : ℂ)*(t : ℂ))=1 := by
    rw [← Complex.exp_add]
    simp
  apply Prod.ext
  · simp [radialExteriorUnweight,radialExteriorErrorMatrix,Complex.real_smul]
    ring
  · simp [radialExteriorUnweight,radialExteriorErrorMatrix,radialExteriorWeightedIncrement,
      Complex.real_smul]
    linear_combination (N (f t+Complex.exp (-((κ : ℂ)*(t : ℂ)))*(v t).1)-N (f t))*hc

theorem radialExteriorUnweight_norm (κ t : ℝ) (v : ℝ → ℂ × ℂ) (C : ℝ)
    (hv : ‖v t‖ ≤ C) :
    ‖radialExteriorUnweight κ v t‖ ≤ Real.exp (-κ*t)*C := by
  simp only [radialExteriorUnweight,norm_smul,Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left hv (Real.exp_nonneg _)

end DefocusingNLS

end OAI
