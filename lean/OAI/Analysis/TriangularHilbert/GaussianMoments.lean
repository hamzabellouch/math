import OAI.Analysis.TriangularHilbert.GaussianConvolution

namespace OAI

section
namespace TriangularHilbert.Heat
open MeasureTheory
open scoped NNReal
noncomputable section

lemma integrable_pow_density {s : ℝ} (hs : 0 < s) (n : ℕ) :
    Integrable (fun x : ℝ => x^n*density s x) := by
  have hi : Integrable (fun x : ℝ => x^n*Real.exp (-(1/(2*s))*x^2)) := by
    simpa only [Real.rpow_natCast] using
      (integrable_rpow_mul_exp_neg_mul_sq (by positivity : 0 < 1/(2*s)) (by have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n; linarith : -1 < (n:ℝ)))
  convert hi.mul_const (Real.sqrt (2*Real.pi*s))⁻¹ using 1
  funext x
  unfold density
  rw [show -(1/(2*s))*x^2 = -x^2/(2*s) by ring]
  ring

lemma integral_density_first (s : ℝ) : (∫ x : ℝ, x*density s x) = 0 := by
  have he := integral_neg_eq_self (fun x : ℝ => x*density s x) volume
  simp only [density_neg,neg_mul,integral_neg] at he
  linarith

lemma integral_density_third (s : ℝ) : (∫ x : ℝ, x^3*density s x) = 0 := by
  have he := integral_neg_eq_self (fun x : ℝ => x^3*density s x) volume
  simp only [density_neg,neg_pow,show (-1:ℝ)^3 = -1 by norm_num,neg_mul,one_mul,integral_neg] at he
  linarith

lemma integral_density_second {s : ℝ} (hs : 0 < s) : (∫ x : ℝ, x^2*density s x) = s := by
  let v : ℝ≥0 := ⟨s,hs.le⟩
  have hv : v ≠ 0 := by
    intro he
    have h := congrArg (fun q : ℝ≥0 => (q:ℝ)) he
    exact hs.ne' h
  have hh := ProbabilityTheory.variance_fun_id_gaussianReal (μ:=0) (v:=v)
  rw [ProbabilityTheory.variance_eq_integral (X := fun x : ℝ => x) (by fun_prop)] at hh
  simp only [ProbabilityTheory.integral_id_gaussianReal,sub_zero] at hh
  rw [ProbabilityTheory.integral_gaussianReal_eq_integral_smul hv] at hh
  change (∫ x : ℝ, ProbabilityTheory.gaussianPDFReal 0 v x * (x^2)) = s at hh
  change (∫ x : ℝ, x^2*density s x) = s
  convert hh using 1
  congr 1
  funext x
  change x^2*((Real.sqrt (2*Real.pi*s))⁻¹*Real.exp (-x^2/(2*s))) =
    ((Real.sqrt (2*Real.pi*s))⁻¹*Real.exp (-((x-0)^2)/(2*s)))*x^2
  simp only [sub_zero]
  ring

def cubic (c0 c1 c2 c3 x : ℝ) : ℝ := c0+c1*x+c2*x^2+c3*x^3

lemma integral_cubic_density {s : ℝ} (hs : 0 < s) (c0 c1 c2 c3 : ℝ) :
    (∫ x : ℝ, cubic c0 c1 c2 c3 x*density s x) = c0+c2*s := by
  have h0 := (density_integrable hs.le).const_mul c0
  have h1 : Integrable (fun x : ℝ => c1*(x*density s x)) := by simpa only [pow_one] using (integrable_pow_density hs 1).const_mul c1
  have h2 := (integrable_pow_density hs 2).const_mul c2
  have h3 := (integrable_pow_density hs 3).const_mul c3
  have he (x : ℝ) : cubic c0 c1 c2 c3 x*density s x =
      (c0*density s x+c1*(x*density s x))+c2*(x^2*density s x)+c3*(x^3*density s x) := by unfold cubic; ring
  simp_rw [he]
  have e3 := integral_add ((h0.add h1).add h2) h3
  have e2 := integral_add (h0.add h1) h2
  have e1 := integral_add h0 h1
  dsimp only [Pi.add_apply] at e1 e2 e3
  rw [e3,e2,e1]
  simp only [integral_const_mul,integral_density hs,integral_density_first,integral_density_second hs,integral_density_third,mul_one,mul_zero,add_zero]

lemma integral_shifted_cubic_density {s : ℝ} (hs : 0 < s) (c0 c1 c2 c3 m : ℝ) :
    (∫ x : ℝ, cubic c0 c1 c2 c3 (x-m)*density s (x-m)) = c0+c2*s := by
  rw [integral_sub_right_eq_self (fun x : ℝ => cubic c0 c1 c2 c3 x*density s x),integral_cubic_density hs]
end
end TriangularHilbert.Heat
end

end OAI
