import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialProductGauge
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.OddPowerNonlinearity

namespace OAI

/-! Radial product jets and the exact two-channel power-polynomial cancellation. -/

namespace DefocusingNLS

 theorem spectralRadialProduct_deriv_two (f g : ℝ → ℂ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (r : ℝ) :
    deriv (deriv (fun t => f t*g t)) r=
      deriv (deriv f) r*g r+2*deriv f r*deriv g r+f r*deriv (deriv g) r := by
  have hf1 : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hg1 : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hf2 : Differentiable ℝ (deriv f) := (hf.deriv' (n := 1)).differentiable (by norm_num)
  have hg2 : Differentiable ℝ (deriv g) := (hg.deriv' (n := 1)).differentiable (by norm_num)
  have hd : deriv (fun t => f t*g t)=fun t => deriv f t*g t+f t*deriv g t := by
    funext t
    exact ((hf1 t).hasDerivAt.mul (hg1 t).hasDerivAt).deriv
  rw [hd]
  calc
    _ = (deriv (deriv f) r*g r+deriv f r*deriv g r)+
        (deriv f r*deriv g r+f r*deriv (deriv g) r) :=
      ((hf2 r).hasDerivAt.mul (hg1 r).hasDerivAt |>.add
        ((hf1 r).hasDerivAt.mul (hg2 r).hasDerivAt)).deriv
    _ = _ := by ring

theorem spectralPowerGauge (m : ℕ) (q u v : ℂ) :
    (((m+1 : ℕ) : ℂ)*q^m*star q^m)*(q*u)+
        ((m : ℂ)*q^(m+1)*star q^(m-1))*(star q*v)=
      ((‖q‖^(2*m) : ℝ) : ℂ)*q*(((m+1 : ℕ) : ℂ)*u+(m : ℂ)*v) := by
  rw [← oddPowerNonlinearity_eq]
  cases m with
  | zero => simp [oddPowerNonlinearity]
  | succ m =>
    simp only [oddPowerNonlinearity,Nat.succ_sub_one,pow_succ,Nat.cast_add,Nat.cast_one]
    ring

theorem spectralPowerGauge_conjugate (m : ℕ) (q u v : ℂ) :
    star (((m+1 : ℕ) : ℂ)*q^m*star q^m)*(star q*v)+
        star ((m : ℂ)*q^(m+1)*star q^(m-1))*(q*u)=
      ((‖q‖^(2*m) : ℝ) : ℂ)*star q*(((m+1 : ℕ) : ℂ)*v+(m : ℂ)*u) := by
  have h := spectralPowerGauge m (star q) v u
  simp only [star_mul,star_pow,star_star,star_natCast]
  simp only [star_star,norm_star] at h
  convert h using 1
  ring

theorem spectralRadialLinearizedProduct (m : ℕ)
    (r a b η q dq ddq u du ddu v : ℂ) (hq : q ≠ 0)
    (hstat : Complex.I*(ddq+11/r*dq)-r/2*dq+(-a+Complex.I*b)*q-
      Complex.I*((‖q‖^(2*m) : ℝ) : ℂ)*q=0) :
    Complex.I*(ddq*u+2*dq*du+q*ddu+11/r*(dq*u+q*du)-η/r^2*(q*u))-
      r/2*(dq*u+q*du)+(-a+Complex.I*b)*(q*u)-Complex.I*
        ((((m+1 : ℕ) : ℂ)*q^m*star q^m)*(q*u)+
          ((m : ℂ)*q^(m+1)*star q^(m-1))*(star q*v))=
    q*(Complex.I*(ddu+(11/r+2*dq/q)*du-η/r^2*u)-r/2*du-
      Complex.I*(m : ℂ)*((‖q‖^(2*m) : ℝ) : ℂ)*(u+v)) := by
  rw [spectralPowerGauge]
  have h := spectralRadialProductGauge r a b ((‖q‖^(2*m) : ℝ) : ℂ)
    η 1 q dq ddq u du ddu hq (by simpa only [one_mul] using hstat)
  simp only [one_mul] at h
  push_cast at h ⊢
  linear_combination h

theorem spectralRadialLinearizedConjugate (m : ℕ)
    (r a b η q dq ddq u du ddu v : ℂ) (hq : star q ≠ 0)
    (hstat : -Complex.I*(ddq+11/r*dq)-r/2*dq+(-a-Complex.I*b)*star q+
      Complex.I*((‖q‖^(2*m) : ℝ) : ℂ)*star q=0) :
    -Complex.I*(ddq*u+2*dq*du+star q*ddu+11/r*(dq*u+star q*du)-η/r^2*(star q*u))-
      r/2*(dq*u+star q*du)+(-a-Complex.I*b)*(star q*u)+Complex.I*
        (star (((m+1 : ℕ) : ℂ)*q^m*star q^m)*(star q*u)+
          star ((m : ℂ)*q^(m+1)*star q^(m-1))*(q*v))=
    star q*(-Complex.I*(ddu+(11/r+2*dq/star q)*du-η/r^2*u)-r/2*du+
      Complex.I*(m : ℂ)*((‖q‖^(2*m) : ℝ) : ℂ)*(u+v)) := by
  rw [spectralPowerGauge_conjugate]
  have h := spectralRadialProductGauge r a b ((‖q‖^(2*m) : ℝ) : ℂ)
    η (-1) (star q) dq ddq u du ddu hq (by
      simpa only [neg_mul,one_mul,mul_neg,neg_neg,sub_eq_add_neg] using hstat)
  simp only [neg_mul,one_mul] at h
  push_cast at h ⊢
  linear_combination h

end DefocusingNLS

end OAI
