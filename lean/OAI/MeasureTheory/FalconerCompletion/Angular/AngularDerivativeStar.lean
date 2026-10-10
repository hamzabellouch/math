import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Angular.AngularWordOperatorBound
import OAI.MeasureTheory.FalconerCompletion.Graphs.NormalizedAngularWord2

namespace OAI

/-! Angular cutoffs and derivative estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell
open scoped ContDiff
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma angularDerivativeND_star (A : V →L[ℝ] V) (f : V → ℂ) :
    angularDerivativeND A (fun x => star (f x)) = fun x => star (angularDerivativeND A f x) := by
  funext x
  simp only [angularDerivativeND,fderiv_star,ContinuousLinearMap.comp_apply]
  rfl

lemma angularDerivativeND_even (A : V →L[ℝ] V) {f : V → ℂ}
    (hf : ContDiff ℝ ∞ f) (he : Function.Even f) : Function.Even (angularDerivativeND A f) := by
  have heq : f ∘ (fun x : V => -x) = f := funext he
  intro x
  have hd := fderiv_comp (𝕜 := ℝ) x (hf.differentiable (by simp) (-x))
    (differentiableAt_id.neg : DifferentiableAt ℝ (fun y : V => -y) x)
  have hneg : fderiv ℝ (fun y : V => -y) x = -ContinuousLinearMap.id ℝ V :=
    ContinuousLinearMap.fderiv (-ContinuousLinearMap.id ℝ V)
  rw [heq,hneg] at hd
  have hh := congrArg (fun T : V →L[ℝ] ℂ => T (A x)) hd
  simpa only [angularDerivativeND,Function.comp_apply,map_neg,ContinuousLinearMap.comp_apply,
    fderiv_fun_neg,fderiv_fun_id,neg_apply,ContinuousLinearMap.id_apply] using hh.symm

noncomputable def smoothStarND (f : SmoothFunctionND V) : SmoothFunctionND V :=
  ⟨fun x => star (f.1 x), by
    change ContDiff ℝ ∞ (fun x => star (f.1 x))
    simpa only [Complex.star_def,Function.comp_def,Complex.conjCLE_apply] using
      Complex.conjCLE.contDiff.comp (smoothFunctionND_contDiff f)⟩

lemma angularWordOperatorND_star (L : List (V →L[ℝ] V)) (f : SmoothFunctionND V) :
    angularWordOperatorND L (smoothStarND f)=smoothStarND (angularWordOperatorND L f) := by
  induction L with
  | nil => rfl
  | cons A L ih =>
    change angularOperatorND A (angularWordOperatorND L (smoothStarND f)) = _
    rw [ih]
    apply Subtype.ext
    exact angularDerivativeND_star A _

lemma angularWordOperatorND_even (L : List (V →L[ℝ] V)) (f : SmoothFunctionND V)
    (he : Function.Even f.1) : Function.Even (angularWordOperatorND L f).1 := by
  induction L with
  | nil => exact he
  | cons A L ih =>
    exact angularDerivativeND_even A (smoothFunctionND_contDiff _) ih

lemma normalizedAngularWordND_even (A : ℝ) (L : List (V →L[ℝ] V)) (f : SmoothFunctionND V)
    (he : Function.Even f.1) : Function.Even (normalizedAngularWordND A L f).1 := by
  intro x
  change ((A:ℂ)^L.length)⁻¹ * (angularWordOperatorND L f).1 (-x) =
    ((A:ℂ)^L.length)⁻¹ * (angularWordOperatorND L f).1 x
  rw [angularWordOperatorND_even L f he x]

lemma normalizedAngularWordND_star (A : ℝ) (L : List (V →L[ℝ] V)) (f : SmoothFunctionND V) :
    normalizedAngularWordND A L (smoothStarND f) = smoothStarND (normalizedAngularWordND A L f) := by
  apply Subtype.ext
  funext x
  simp only [normalizedAngularWordND,angularWordOperatorND_star]
  change ((A:ℂ)^L.length)⁻¹ * star ((angularWordOperatorND L f).1 x) =
    star (((A:ℂ)^L.length)⁻¹ * (angularWordOperatorND L f).1 x)
  simp only [map_mul,map_inv₀,map_pow,Complex.star_def,Complex.conj_ofReal]

end Attempt4PrefixShell
end GraphLiteralSupport
end
end

end OAI
