import OAI.Combinatorics.PolynomialVacuum.Puncture.Reference

namespace OAI

namespace PolynomialVacuumCylinder
open Real MeasureTheory Set

 
theorem polynomial_laplace_integral (m : ℕ) {a : ℝ} (ha : 0<a) :
    (∫ x : ℝ in Ioi 0,x^m*Real.exp (-a*x))=(m.factorial : ℝ)/a^(m+1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a:=(m : ℝ)+1) (r:=a) (by positivity) ha
  rw [show (m : ℝ)+1-1=(m : ℝ) by ring] at h
  simp only [Real.rpow_natCast,Real.Gamma_nat_eq_factorial] at h
  have hp : (1/a)^((m : ℝ)+1)=(1/a)^(m+1) := by
    rw [←Nat.cast_add_one,Real.rpow_natCast]
  rw [hp,one_div_pow] at h
  simpa only [neg_mul,mul_neg,div_eq_mul_inv,one_mul,mul_one,mul_comm] using h

 
theorem odd_moment_summable (m : ℕ) :
    Summable (fun k : ℕ=>(1 : ℝ)/(2*(k : ℝ)+1)^(2*m+2)) := by
  have h := (Real.summable_one_div_nat_pow.mpr (by omega : 1<2*m+2)).comp_injective
    (show Function.Injective (fun k : ℕ=>2*k+1) by intro i j hij; change 2*i+1=2*j+1 at hij; omega)
  simpa only [Function.comp_def,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using h

noncomputable def referenceMomentTerm (m : ℕ) (a : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  (1/2)*x^(2*m+1)*Real.exp (-(a*(2*(k : ℝ)+1))*x)

theorem referenceMomentTerm_integrable (m : ℕ) {a : ℝ} (ha : 0<a) (k : ℕ) :
    IntegrableOn (referenceMomentTerm m a k) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s:=((2*m+1 : ℕ) : ℝ)) (p:=1)
    (by have := Nat.cast_nonneg (α:=ℝ) (2*m+1); linarith) (by norm_num)
    (mul_pos ha (show 0<2*(k : ℝ)+1 by positivity))
  have hi : IntegrableOn (fun x : ℝ=>x^(2*m+1)*Real.exp (-(a*(2*(k : ℝ)+1))*x)) (Ioi 0) := by
    simpa only [Real.rpow_natCast,Real.rpow_one] using h
  apply (hi.const_mul (1/2)).congr
  filter_upwards [] with x
  dsimp [referenceMomentTerm]
  ring

theorem referenceMomentTerm_integral (m : ℕ) {a : ℝ} (ha : 0<a) (k : ℕ) :
    (∫ x : ℝ in Ioi 0,referenceMomentTerm m a k x)=
      ((2*m+1).factorial : ℝ)/(2*a^(2*m+2)) * (1/(2*(k : ℝ)+1)^(2*m+2)) := by
  unfold referenceMomentTerm
  have hf : (fun x : ℝ=>(1/2)*x^(2*m+1)*Real.exp (-(a*(2*(k : ℝ)+1))*x))=
      (fun x : ℝ=>(1/2)*(x^(2*m+1)*Real.exp (-(a*(2*(k : ℝ)+1))*x))) := by funext x; ring
  rw [hf,integral_const_mul,polynomial_laplace_integral _ (mul_pos ha (by positivity))]
  rw [mul_pow]
  field_simp

theorem referenceMoment_series (m : ℕ) {a x : ℝ} (ha : 0<a) (hx : 0<x) :
    HasSum (fun k=>referenceMomentTerm m a k x) (x^(2*m)*(x/(4*Real.sinh (a*x)))) := by
  have hr : ‖Real.exp (-2*a*x)‖<1 := by
    rw [Real.norm_of_nonneg (Real.exp_pos _).le,Real.exp_lt_one_iff]
    nlinarith
  have h := (hasSum_geometric_of_norm_lt_one hr).mul_left
    ((1/2)*x^(2*m+1)*Real.exp (-a*x))
  have hf : (fun k : ℕ=>((1/2)*x^(2*m+1)*Real.exp (-a*x))*Real.exp (-2*a*x)^k)=
      (fun k=>referenceMomentTerm m a k x) := by
    funext k
    rw [←Real.exp_nat_mul]
    unfold referenceMomentTerm
    calc
      _ = ((1/2)*x^(2*m+1))*(Real.exp (-a*x)*Real.exp ((k : ℝ)*(-2*a*x))) := by ring
      _ = _ := by rw [←Real.exp_add]; congr 2; ring
  rw [hf] at h
  suffices hv : (1/2)*x^(2*m+1)*Real.exp (-a*x)*(1-Real.exp (-2*a*x))⁻¹ =
      x^(2*m)*(x/(4*Real.sinh (a*x))) by exact hv ▸ h
  have he : Real.exp (-a*x)=1/Real.exp (a*x) := by rw [one_div,←Real.exp_neg]; congr 1; ring
  have he2 : Real.exp (-2*a*x)=(1/Real.exp (a*x))^2 := by
    rw [←he,←Real.exp_nat_mul]; congr 1; ring
  have hs : Real.sinh (a*x)≠0 := (Real.sinh_pos_iff.mpr (mul_pos ha hx)).ne'
  have he0 : Real.exp (a*x)≠0 := (Real.exp_pos _).ne'
  rw [he,he2,Real.sinh_eq,Real.exp_neg]
  rw [pow_succ]
  field_simp
  ring

end PolynomialVacuumCylinder

end OAI
