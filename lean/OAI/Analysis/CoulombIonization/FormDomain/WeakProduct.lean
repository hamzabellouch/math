import Mathlib
import OAI.Analysis.CoulombIonization.FormDomain.WeakDerivative

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
namespace CoulombAtom
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [IsLocallyFiniteMeasure (volume : Measure E)]

omit [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [IsLocallyFiniteMeasure (volume : Measure E)] in
lemma smooth_lineDeriv_mul {p φ : E → ℝ} (hp : ContDiff ℝ ∞ p)
    (hφ : ContDiff ℝ ∞ φ) (x v : E) :
    lineDeriv ℝ (fun y => p y * φ y) x v =
      lineDeriv ℝ p x v * φ x + p x * lineDeriv ℝ φ x v := by
  rw [((hp.mul hφ).differentiable (by simp) x).lineDeriv_eq_fderiv,
    (hp.differentiable (by simp) x).lineDeriv_eq_fderiv,
    (hφ.differentiable (by simp) x).lineDeriv_eq_fderiv]
  change (fderiv ℝ (p * φ) x) v = _
  rw [fderiv_mul (hp.differentiable (by simp) x) (hφ.differentiable (by simp) x)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

lemma IsWeakDerivative.mul_smooth {f g : E → ℂ} {v : E}
    (hw : IsWeakDerivative v f g) (hf : MemLp f 2) (hg : MemLp g 2)
    {p : E → ℝ} (hp : ContDiff ℝ ∞ p) :
    IsWeakDerivative v (fun x => (p x : ℂ) * f x)
      (fun x => (p x : ℂ) * g x + Complex.ofReal (lineDeriv ℝ p x v) * f x) := by
  intro φ hφ hcφ
  have htest := hw (fun x => p x * φ x) (hp.mul hφ) hcφ.mul_left
  have hdφ : Continuous (fun x => lineDeriv ℝ φ x v) := by
    have he : (fun x => lineDeriv ℝ φ x v) = fun x => fderiv ℝ φ x v := by
      funext x
      exact (hφ.differentiable (by simp) x).lineDeriv_eq_fderiv
    rw [he]
    exact (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdp : Continuous (fun x => lineDeriv ℝ p x v) := by
    have he : (fun x => lineDeriv ℝ p x v) = fun x => fderiv ℝ p x v := by
      funext x
      exact (hp.differentiable (by simp) x).lineDeriv_eq_fderiv
    rw [he]
    exact (hp.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcdφ : HasCompactSupport (fun x => lineDeriv ℝ φ x v) := by
    have he : (fun x => lineDeriv ℝ φ x v) = fun x => fderiv ℝ φ x v := by
      funext x
      exact (hφ.differentiable (by simp) x).lineDeriv_eq_fderiv
    rw [he]
    exact (hcφ.fderiv ℝ).comp_left (g := fun A : E →L[ℝ] ℝ => A v) (by simp)
  have him (q : E → ℝ) (hq : Continuous q) (hcq : HasCompactSupport q)
      (u : E → ℂ) (hu : MemLp u 2) : Integrable (fun x => (q x : ℂ) * u x) := by
    have hq2 : MemLp (fun x => (q x : ℂ)) 2 :=
      (Complex.continuous_ofReal.comp hq).memLp_of_hasCompactSupport
        (hcq.comp_left (g := Complex.ofReal) (by rfl))
    exact hq2.integrable_mul hu
  have i1 := him (fun x => p x * lineDeriv ℝ φ x v)
    (hp.continuous.mul hdφ) hcdφ.mul_left f hf
  have i2 := him (fun x => lineDeriv ℝ p x v * φ x)
    (hdp.mul hφ.continuous) hcφ.mul_left f hf
  have i3 := him (fun x => p x * φ x)
    (hp.continuous.mul hφ.continuous) hcφ.mul_left g hg
  have he1 : (fun x => f x * Complex.ofReal (lineDeriv ℝ (fun y => p y * φ y) x v)) =
      fun x => ((lineDeriv ℝ p x v * φ x : ℝ) : ℂ) * f x +
        ((p x * lineDeriv ℝ φ x v : ℝ) : ℂ) * f x := by
    funext x
    rw [smooth_lineDeriv_mul hp hφ]
    push_cast
    ring
  rw [he1, integral_add i2 i1] at htest
  have he2 : (fun x => g x * ((p x * φ x : ℝ) : ℂ)) =
      fun x => ((p x * φ x : ℝ) : ℂ) * g x := by
    funext x
    ring
  rw [he2] at htest
  have he3 : (fun x => (p x : ℂ) * f x * Complex.ofReal (lineDeriv ℝ φ x v)) =
      fun x => ((p x * lineDeriv ℝ φ x v : ℝ) : ℂ) * f x := by
    funext x
    push_cast
    ring
  have he4 : (fun x => ((p x : ℂ) * g x + Complex.ofReal (lineDeriv ℝ p x v) * f x) * (φ x : ℂ)) =
      fun x => ((p x * φ x : ℝ) : ℂ) * g x +
        ((lineDeriv ℝ p x v * φ x : ℝ) : ℂ) * f x := by
    funext x
    push_cast
    ring
  rw [he3, he4, integral_add i3 i2]
  linear_combination htest

end CoulombAtom

end

end OAI
