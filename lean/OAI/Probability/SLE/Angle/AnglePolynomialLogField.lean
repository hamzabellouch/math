import OAI.Probability.SLE.Angle.AngleLogGeneratorCoefficients

namespace OAI

/-! Smooth Green-weighted polynomial tests in the actual Loewner state. -/
noncomputable section
open Polynomial

namespace SLEExactGauge

def logPolynomialDensity (κ p a : ℝ) (P : ℝ[X]) (q : ℂ × ℝ) (x : ℝ) : ℝ :=
  powerLogDensity κ p a q x*P.eval (logCosine κ q x)

private lemma polynomial_eval_contDiff (P : ℝ[X]) (n : WithTop ℕ∞) :
    ContDiff ℝ n (fun x => P.eval x) := by
  simpa using P.contDiff_aeval (𝕜 := ℝ) n

lemma logPolynomialDensity_contDiff (κ p a : ℝ) (P : ℝ[X]) :
    ContDiff ℝ (⊤:ℕ∞) (fun z : (ℂ × ℝ) × ℝ => logPolynomialDensity κ p a P z.1 z.2) :=
  (powerLogDensity_contDiff κ p a).mul
    ((polynomial_eval_contDiff P _).comp (logCosine_contDiff κ))

private lemma real_second_mul {f g : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : ℝ) :
    iteratedDeriv 2 (fun y => f y*g y) x=
      iteratedDeriv 2 f x*g x+2*deriv f x*deriv g x+f x*iteratedDeriv 2 g x := by
  have hf1 := hf.differentiable (by norm_num)
  have hg1 := hg.differentiable (by norm_num)
  have hd : deriv (fun y => f y*g y)=fun y => deriv f y*g y+f y*deriv g y :=
    funext (fun y => deriv_mul (hf1 y) (hg1 y))
  have hh := (((hf.differentiable_deriv_two x).hasDerivAt).mul (hg1 x).hasDerivAt).add
    ((hf1 x).hasDerivAt.mul (hg.differentiable_deriv_two x).hasDerivAt)
  change HasDerivAt (fun y => deriv f y*g y+f y*deriv g y) _ x at hh
  conv_lhs => rw [show (2:ℕ)=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_one]
  rw [hd,hh.deriv]
  have hff : iteratedDeriv 2 f x=deriv (deriv f) x := by
    rw [show (2:ℕ)=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_one]
  have hgg : iteratedDeriv 2 g x=deriv (deriv g) x := by
    rw [show (2:ℕ)=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_one]
  rw [hff,hgg]
  ring

private lemma polynomial_second (P : ℝ[X]) (x : ℝ) :
    iteratedDeriv 2 (fun y => P.eval y) x=P.derivative.derivative.eval x := by
  have hd : deriv (fun y => P.eval y)=fun y => P.derivative.eval y :=
    funext (fun y => P.deriv)
  rw [show (2:ℕ)=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_one,hd]
  exact P.derivative.deriv

lemma logPolynomialDensity_second (κ p a : ℝ) (P : ℝ[X]) (q : ℂ × ℝ) (x : ℝ) :
    iteratedDeriv 2 (logPolynomialDensity κ p a P q) x=
      iteratedDeriv 2 (powerLogDensity κ p a q) x*P.eval (logCosine κ q x)+
      2*deriv (powerLogDensity κ p a q) x*P.derivative.eval (logCosine κ q x)*
        deriv (logCosine κ q) x+
      powerLogDensity κ p a q x*(P.derivative.derivative.eval (logCosine κ q x)*
        (deriv (logCosine κ q) x)^2+
        P.derivative.eval (logCosine κ q x)*iteratedDeriv 2 (logCosine κ q) x) := by
  have hH : ContDiff ℝ 2 (powerLogDensity κ p a q) :=
    ((powerLogDensity_contDiff κ p a).comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)
  have hC : ContDiff ℝ 2 (logCosine κ q) :=
    ((logCosine_contDiff κ).comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)
  have hP := (polynomial_eval_contDiff P 2).comp hC
  change ContDiff ℝ 2 (fun y => P.eval (logCosine κ q y)) at hP
  have hp1 := (P.hasDerivAt (logCosine κ q x)).comp x
    (hC.differentiable (by norm_num) x).hasDerivAt
  have hp2 := iteratedDeriv_comp_two (x := x)
    (polynomial_eval_contDiff P 2).contDiffAt hC.contDiffAt
  change iteratedDeriv 2 (fun y => P.eval (logCosine κ q y)) x = _ at hp2
  have hp1d := hp1.deriv
  change deriv (fun y => P.eval (logCosine κ q y)) x = _ at hp1d
  change iteratedDeriv 2 (fun y => powerLogDensity κ p a q y*P.eval (logCosine κ q y)) x=_
  rw [real_second_mul hH hP x,hp1d,hp2,polynomial_second,P.deriv]
  ring

lemma logPolynomialDensity_directional (κ p a : ℝ) (P : ℝ[X]) (q v : ℂ × ℝ) (x : ℝ) :
    fderiv ℝ (fun r : ℂ × ℝ => logPolynomialDensity κ p a P r x) q v=
      fderiv ℝ (fun r : ℂ × ℝ => powerLogDensity κ p a r x) q v*P.eval (logCosine κ q x)+
      powerLogDensity κ p a q x*P.derivative.eval (logCosine κ q x)*
        fderiv ℝ (fun r : ℂ × ℝ => logCosine κ r x) q v := by
  have hH : Differentiable ℝ (fun r : ℂ × ℝ => powerLogDensity κ p a r x) :=
    ((powerLogDensity_contDiff κ p a).comp
    (contDiff_id.prodMk contDiff_const)).differentiable (by simp)
  have hC : Differentiable ℝ (fun r : ℂ × ℝ => logCosine κ r x) :=
    ((logCosine_contDiff κ).comp
    (contDiff_id.prodMk contDiff_const)).differentiable (by simp)
  have hp := (P.hasDerivAt (logCosine κ q x)).comp_hasFDerivAt q (hC q).hasFDerivAt
  have he := congrArg (fun L : (ℂ × ℝ) →L[ℝ] ℝ => L v) ((hH q).hasFDerivAt.mul hp).fderiv
  change fderiv ℝ (fun r : ℂ × ℝ => logPolynomialDensity κ p a P r x) q v=_ at he
  rw [he]
  simp only [add_apply,smul_apply,smul_eq_mul,Function.comp_apply]
  ring

end SLEExactGauge

end

end OAI
