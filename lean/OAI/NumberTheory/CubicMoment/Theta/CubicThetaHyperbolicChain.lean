import OAI.NumberTheory.CubicMoment.Theta.CubicThetaSecondChain

namespace OAI

/-! The hyperbolic chain rule, keeping the two coefficients explicit.
They will be identified for the actual arithmetic row height using its
already proved first and second power equations. -/
noncomputable section
open scoped ContDiff
namespace CubicFirstMoment

def cubicThetaHeightChainQuadratic (h : ℝ → ℝ → ℝ → ℝ) (x y v : ℝ) : ℂ :=
  (v:ℂ)^2*(((deriv (fun t => h t y v) x:ℝ):ℂ)^2+
    ((deriv (fun t => h x t v) y:ℝ):ℂ)^2+
    ((deriv (fun t => h x y t) v:ℝ):ℂ)^2)

def cubicThetaHeightChainLinear (h : ℝ → ℝ → ℝ → ℝ) (x y v : ℝ) : ℂ :=
  (v:ℂ)^2*(((deriv (deriv (fun t => h t y v)) x:ℝ):ℂ)+
    ((deriv (deriv (fun t => h x t v)) y:ℝ):ℂ)+
    ((deriv (deriv (fun t => h x y t)) v:ℝ):ℂ))-
    (v:ℂ)*((deriv (fun t => h x y t) v:ℝ):ℂ)

theorem cubicThetaHyperbolic_chain {h : ℝ → ℝ → ℝ → ℝ} {f : ℝ → ℂ} {x y v : ℝ}
    (hx : ContDiffAt ℝ 2 (fun t => h t y v) x)
    (hy : ContDiffAt ℝ 2 (fun t => h x t v) y)
    (hv : ContDiffAt ℝ 2 (fun t => h x y t) v)
    (hf : ContDiffAt ℝ 2 f (h x y v)) :
    cubicThetaHyperbolicOperator (fun a b t => f (h a b t)) x y v=
      cubicThetaHeightChainQuadratic h x y v*deriv (deriv f) (h x y v)+
      cubicThetaHeightChainLinear h x y v*deriv f (h x y v) := by
  have hxx := cubicThetaSecondChain (h:=fun t => h t y v) (x:=x) hf hx
  have hyy := cubicThetaSecondChain (h:=fun t => h x t v) (x:=y) hf hy
  have hvv := cubicThetaSecondChain (h:=fun t => h x y t) (x:=v) hf hv
  have hdv := deriv.scomp v (hf.differentiableAt (by norm_num))
    (hv.differentiableAt (by norm_num))
  simp only [Function.comp_def] at hxx hyy hvv hdv
  unfold cubicThetaHyperbolicOperator cubicThetaHeightChainQuadratic cubicThetaHeightChainLinear
  dsimp only
  rw [hxx,hyy,hvv,hdv]
  simp only [Complex.real_smul,Complex.ofReal_pow]
  ring

end CubicFirstMoment

end

end OAI
