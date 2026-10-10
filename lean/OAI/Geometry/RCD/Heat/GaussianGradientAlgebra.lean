import Mathlib

namespace OAI

/-! # Scalar constants in the Gaussian gradient estimate -/

namespace RegularPointCoordinates

/-- The local square estimate from reverse Poincaré gives a Gaussian
bound for the gradient, with one uniform enlarged coefficient. -/
theorem gaussian_gradient_algebra {C D V t r k B d g : ℝ}
    (hC : 0 < C) (hD : 1 ≤ D) (hV : 0 < V) (ht : 0 < t) (hr : 0 < r)
    (hr2 : r^2 = t) (hk : 0 ≤ k)
    (hg : (t*Real.exp (-k*t))*g^2 ≤
      (C*D/V*Real.exp (B*t))*(C*Real.exp 1/V*Real.exp (-d^2/(10*t)+B*t))) :
    g ≤ (C*D*Real.exp 1/(r*V))*Real.exp (-d^2/(20*t)+(B+k)*t) := by
  let E := Real.exp (-d^2/(20*t)+(B+k)*t)
  let A := C*D*Real.exp 1
  let Q := (C*D/V*Real.exp (B*t))*(C*Real.exp 1/V*Real.exp (-d^2/(10*t)+B*t))
  have hEe : Real.exp (-k*t)*E^2 =
      Real.exp (k*t)*(Real.exp (B*t)*Real.exp (-d^2/(10*t)+B*t)) := by
    dsimp [E]
    rw [← Real.exp_nat_mul,← Real.exp_add,← Real.exp_add,← Real.exp_add]
    congr 1
    ring
  have heq : (t*Real.exp (-k*t))*(A/(r*V)*E)^2 =
      (D*Real.exp 1*Real.exp (k*t))*Q := by
    calc
      _ = (C^2*D^2*(Real.exp 1)^2/V^2)*(Real.exp (-k*t)*E^2) := by
        dsimp [A]
        field_simp
        rw [hr2]
      _ = _ := by
        rw [hEe]
        dsimp [Q]
        field_simp
  have hfactor : 1 ≤ D*Real.exp 1*Real.exp (k*t) := by
    have he : 1 ≤ Real.exp (1:ℝ) := Real.one_le_exp_iff.mpr (by norm_num)
    have hk' : 1 ≤ Real.exp (k*t) := Real.one_le_exp_iff.mpr (mul_nonneg hk ht.le)
    have hDE : 1 ≤ D*Real.exp 1 := by nlinarith
    exact hDE.trans (le_mul_of_one_le_right (by linarith) hk')
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hG : (t*Real.exp (-k*t))*g^2 ≤ (t*Real.exp (-k*t))*(A/(r*V)*E)^2 := by
    rw [heq]
    exact hg.trans (by nlinarith)
  change g ≤ A/(r*V)*E
  have hAn : 0 ≤ A := by dsimp [A]; positivity
  have hEn : 0 ≤ E := (Real.exp_pos _).le
  apply le_of_sq_le_sq ((mul_le_mul_iff_right₀ (by positivity : 0 < t*Real.exp (-k*t))).mp ?_)
    (mul_nonneg (div_nonneg hAn (mul_pos hr hV).le) hEn)
  simpa only [mul_comm] using! hG

/-- The same envelope dominates the local amplitude. -/
theorem gaussian_amplitude_algebra {C D V t k B d : ℝ}
    (hC : 0 < C) (hD : 1 ≤ D) (hV : 0 < V) (ht : 0 < t) (hk : 0 ≤ k) :
    C*Real.exp 1/V*Real.exp (-d^2/(10*t)+B*t) ≤
      C*D*Real.exp 1/V*Real.exp (-d^2/(20*t)+(B+k)*t) := by
  have he : -d^2/(10*t)+B*t ≤ -d^2/(20*t)+(B+k)*t := by
    have hpos := div_nonneg (sq_nonneg d) (show 0 ≤ 20*t by positivity)
    have hmul := mul_nonneg hk ht.le
    field_simp
    nlinarith
  apply mul_le_mul _ (Real.exp_le_exp.mpr he) (Real.exp_pos _).le
    (by positivity)
  apply div_le_div_of_nonneg_right _ hV.le
  have hh := mul_le_mul_of_nonneg_left hD (show 0 ≤ C*Real.exp 1 by positivity)
  nlinarith only [hh]

/-- The cutoff coefficient has exactly the required heat-length scaling. -/
theorem gaussian_cutoff_factor {A E r V : ℝ} (hA : 0 ≤ A) (hE : 0 ≤ E)
    (hr : 0 < r) (hV : 0 < V) :
    Real.sqrt (2*(A/(r*V)*E)^2+2*(A/V*E)^2*(r⁻¹)^2) =
      2*A/(r*V)*E := by
  have heq : 2*(A/(r*V)*E)^2+2*(A/V*E)^2*(r⁻¹)^2 = (2*A/(r*V)*E)^2 := by
    field_simp
    ring
  rw [heq,Real.sqrt_sq_eq_abs,abs_of_nonneg]
  positivity

end RegularPointCoordinates

end OAI
