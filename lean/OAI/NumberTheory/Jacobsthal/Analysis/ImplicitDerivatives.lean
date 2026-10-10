import OAI.NumberTheory.Jacobsthal.Estimates.BivariateCalculus

namespace OAI

namespace Erdos970

section

open Filter
open scoped Topology
namespace ErdosImplicitCurvature

theorem graph_zero_near (Q : Bivariate) (f : ℝ → ℝ) {I : Set ℝ} (hI : IsOpen I)
    (hcurve : ∀ t ∈ I, peval Q t (f t) = 0) {x : ℝ} (hx : x ∈ I) :
    (fun t => peval Q t (f t)) =ᶠ[𝓝 x] (fun _ => 0) := by
  filter_upwards [hI.mem_nhds hx] with t ht
  exact hcurve t ht

theorem implicit_first_equation (Q : Bivariate) (f : ℝ → ℝ) {I : Set ℝ}
    (hI : IsOpen I) (hf : DifferentiableOn ℝ f I)
    (hcurve : ∀ t ∈ I, peval Q t (f t) = 0) {x : ℝ} (hx : x ∈ I) :
    peval (partialX Q) x (f x)+peval (partialY Q) x (f x)*deriv f x = 0 := by
  have hd := hasDerivAt_peval_graph Q f (deriv f x) x
    (hf.differentiableAt (hI.mem_nhds hx)).hasDerivAt
  have hz := (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq
    (graph_zero_near Q f hI hcurve hx)
  exact hd.unique hz

theorem implicit_first_derivative (Q : Bivariate) (f : ℝ → ℝ) {I : Set ℝ}
    (hI : IsOpen I) (hf : DifferentiableOn ℝ f I)
    (hcurve : ∀ t ∈ I, peval Q t (f t) = 0) {x : ℝ} (hx : x ∈ I)
    (hQy : peval (partialY Q) x (f x) ≠ 0) :
    deriv f x = -peval (partialX Q) x (f x)/peval (partialY Q) x (f x) := by
  apply (eq_div_iff hQy).mpr
  have h := implicit_first_equation Q f hI hf hcurve hx
  nlinarith only [h]

theorem implicit_second_equation (Q : Bivariate) (f : ℝ → ℝ) {I : Set ℝ}
    (hI : IsOpen I) (hf : ContDiffOn ℝ 2 f I)
    (hcurve : ∀ t ∈ I, peval Q t (f t) = 0) {x : ℝ} (hx : x ∈ I) :
    peval (partialX (partialX Q)) x (f x) +
      2*peval (partialX (partialY Q)) x (f x)*deriv f x +
      peval (partialY (partialY Q)) x (f x)*(deriv f x)^2 +
      peval (partialY Q) x (f x)*deriv (deriv f) x = 0 := by
  have hf1 : DifferentiableOn ℝ f I := hf.differentiableOn (by norm_num)
  have hdf : ContDiffOn ℝ 1 (deriv f) I := hf.deriv_of_isOpen hI (by norm_num)
  have hd1 := (hf1.differentiableAt (hI.mem_nhds hx)).hasDerivAt
  have hd2 := ((hdf.differentiableOn (by norm_num)).differentiableAt (hI.mem_nhds hx)).hasDerivAt
  have hPx := hasDerivAt_peval_graph (partialX Q) f (deriv f x) x hd1
  have hPy := hasDerivAt_peval_graph (partialY Q) f (deriv f x) x hd1
  have hactual := hPx.add (hPy.mul hd2)
  have he : (fun t => peval (partialX Q) t (f t)+peval (partialY Q) t (f t)*deriv f t)
      =ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [hI.mem_nhds hx] with t ht
    exact implicit_first_equation Q f hI hf1 hcurve ht
  have hz := (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq he
  have h := hactual.unique hz
  rw [mixed_partials Q] at h
  linear_combination h

end ErdosImplicitCurvature

end

end Erdos970

end OAI
