import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHyperbolicOperator
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGridEquation
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

namespace OAI

/-! Locality and finite additivity of the actual hyperbolic operator
for twice continuously differentiable functions. -/
noncomputable section
open Filter
open scoped Topology ContDiff
namespace CubicFirstMoment

lemma cubicThetaHyperbolicOperator_germ {F G : ℂ × ℝ → ℂ} (x y v : ℝ)
    (h : F =ᶠ[𝓝 (cubicThetaCartesianPoint x y v)] G) :
    cubicThetaHyperbolicOperator (fun a b t => F (cubicThetaCartesianPoint a b t)) x y v=
      cubicThetaHyperbolicOperator (fun a b t => G (cubicThetaCartesianPoint a b t)) x y v := by
  have hx : Continuous (fun t : ℝ => cubicThetaCartesianPoint t y v) :=
    (Complex.continuous_ofReal.add continuous_const).prodMk continuous_const
  have hy : Continuous (fun t : ℝ => cubicThetaCartesianPoint x t v) :=
    (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).prodMk continuous_const
  have ht : Continuous (fun t : ℝ => cubicThetaCartesianPoint x y t) :=
    continuous_const.prodMk continuous_id
  have ex := h.comp_tendsto (hx.tendsto x)
  have ey := h.comp_tendsto (hy.tendsto y)
  have et := h.comp_tendsto (ht.tendsto v)
  dsimp only [Function.comp_def] at ex ey et
  unfold cubicThetaHyperbolicOperator
  rw [ex.deriv.deriv_eq,ey.deriv.deriv_eq,et.deriv.deriv_eq,et.deriv_eq]

lemma cubicThetaHyperbolicOperator_finite {ι : Type*} (S : Finset ι)
    (F : ι → ℝ → ℝ → ℝ → ℂ) (x y v : ℝ)
    (hx : ∀ i∈S, ContDiffAt ℝ 2 (fun t => F i t y v) x)
    (hy : ∀ i∈S, ContDiffAt ℝ 2 (fun t => F i x t v) y)
    (ht : ∀ i∈S, ContDiffAt ℝ 2 (fun t => F i x y t) v) :
    cubicThetaHyperbolicOperator (fun a b t => ∑ i∈S, F i a b t) x y v=
      ∑ i∈S, cubicThetaHyperbolicOperator (F i) x y v := by
  have ex := iteratedDeriv_fun_sum (n:=2) hx
  have ey := iteratedDeriv_fun_sum (n:=2) hy
  have et := iteratedDeriv_fun_sum (n:=2) ht
  simp only [show (2:ℕ)=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_zero] at ex ey et
  have e₁ := deriv_fun_sum (fun i hi => (ht i hi).differentiableAt (by norm_num))
  unfold cubicThetaHyperbolicOperator
  rw [ex,ey,et,e₁]
  simp only [mul_add,Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_sub_distrib]

end CubicFirstMoment

end

end OAI
