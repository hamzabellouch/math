import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRowHeightEquation
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHyperbolicChain

namespace OAI

/-! The two chain coefficients for the literal arithmetic row height
follow from its power-one and power-two spectral equations. -/
noncomputable section
open scoped ContDiff
namespace CubicFirstMoment

def cubicThetaRowHeightCoordinates (r : CubicThetaBottomRow) (x y v : ℝ) : ℝ :=
  r.height (cubicThetaCartesianPoint x y v)

lemma cubicThetaRowHeightCoordinates_contDiff (r : CubicThetaBottomRow)
    (x y : ℝ) {v : ℝ} (hv : 0<v) :
    ContDiffAt ℝ 2 (fun t => cubicThetaRowHeightCoordinates r t y v) x ∧
    ContDiffAt ℝ 2 (fun t => cubicThetaRowHeightCoordinates r x t v) y ∧
    ContDiffAt ℝ 2 (fun t => cubicThetaRowHeightCoordinates r x y t) v := by
  have hr := r.height_contDiffAt (p:=cubicThetaCartesianPoint x y v) hv
  have hx : ContDiff ℝ ∞ (fun t : ℝ => cubicThetaCartesianPoint t y v) :=
    (Complex.ofRealCLM.contDiff.add contDiff_const).prodMk contDiff_const
  have hy : ContDiff ℝ ∞ (fun t : ℝ => cubicThetaCartesianPoint x t v) :=
    (contDiff_const.add (Complex.ofRealCLM.contDiff.mul contDiff_const)).prodMk contDiff_const
  constructor
  · exact (hr.comp x hx.contDiffAt).of_le (by norm_num)
  constructor
  · exact (hr.comp y hy.contDiffAt).of_le (by norm_num)
  · exact (hr.comp v (by unfold cubicThetaCartesianPoint; fun_prop)).of_le (by norm_num)

theorem cubicThetaRowHeight_chain_coefficients (r : CubicThetaBottomRow)
    (x y : ℝ) {v : ℝ} (hv : 0<v) :
    cubicThetaHeightChainQuadratic (cubicThetaRowHeightCoordinates r) x y v=
      (cubicThetaRowHeightCoordinates r x y v:ℂ)^2 ∧
    cubicThetaHeightChainLinear (cubicThetaRowHeightCoordinates r) x y v=
      -(cubicThetaRowHeightCoordinates r x y v:ℂ) := by
  obtain ⟨hx,hy,ht⟩ := cubicThetaRowHeightCoordinates_contDiff r x y hv
  have hp : 0<cubicThetaRowHeightCoordinates r x y v := r.height_pos hv
  have h₁ := cubicThetaHyperbolic_chain hx hy ht
    ((cubicThetaHeightPower_analytic 1 hp).contDiffAt (n:=2))
  have e₁ := cubicThetaRowHeightPower_eigenvalue r 1 x y hv
  change cubicThetaHyperbolicOperator
    (fun a b t => (cubicThetaRowHeightCoordinates r a b t:ℂ)^(1:ℂ)) x y v=_ at e₁
  rw [e₁,cubicThetaHeightPower_second_deriv 1 hp,cubicThetaHeightPower_deriv 1 hp] at h₁
  norm_num at h₁
  have hL : cubicThetaHeightChainLinear (cubicThetaRowHeightCoordinates r) x y v=
      -(cubicThetaRowHeightCoordinates r x y v:ℂ) := h₁.symm
  have h₂ := cubicThetaHyperbolic_chain hx hy ht
    ((cubicThetaHeightPower_analytic 2 hp).contDiffAt (n:=2))
  have e₂ := cubicThetaRowHeightPower_eigenvalue r 2 x y hv
  change cubicThetaHyperbolicOperator
    (fun a b t => (cubicThetaRowHeightCoordinates r a b t:ℂ)^(2:ℂ)) x y v=_ at e₂
  rw [e₂,cubicThetaHeightPower_second_deriv 2 hp,cubicThetaHeightPower_deriv 2 hp,hL] at h₂
  norm_num at h₂
  refine ⟨?_,hL⟩
  linear_combination -(1/2:ℂ)*h₂

theorem cubicThetaRowHeight_operator (r : CubicThetaBottomRow) {f : ℝ → ℂ}
    (x y : ℝ) {v : ℝ} (hv : 0<v)
    (hf : ContDiffAt ℝ 2 f (cubicThetaRowHeightCoordinates r x y v)) :
    cubicThetaHyperbolicOperator (fun a b t => f (cubicThetaRowHeightCoordinates r a b t)) x y v=
      cubicThetaHyperbolicOperator (fun _ _ t => f t) 0 0 (cubicThetaRowHeightCoordinates r x y v) := by
  obtain ⟨hx,hy,ht⟩ := cubicThetaRowHeightCoordinates_contDiff r x y hv
  obtain ⟨hQ,hL⟩ := cubicThetaRowHeight_chain_coefficients r x y hv
  rw [cubicThetaHyperbolic_chain hx hy ht hf,hQ,hL]
  simp only [cubicThetaHyperbolicOperator,deriv_const',deriv_const,zero_add]
  ring

end CubicFirstMoment

end

end OAI
