import Mathlib
import OAI.Geometry.PrescribedRicci.KahlerGradientEnergy
import OAI.Geometry.PrescribedRicci.GlobalKahlerEnergy

namespace OAI

/-! Kahler Energy Chain. -/

section

 
noncomputable section
open Matrix Filter Set Topology MeasureTheory
open scoped ContDiff ComplexOrder Classical
namespace Anticanonical.SourceSmooth
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}

namespace SmoothRealFunction

def compose (φ : SmoothRealFunction A) (F : ℝ → ℝ) (hF : ContDiff ℝ ∞ F) :
    SmoothRealFunction A where
  value x := F (φ.value x)
  smooth i := hF.comp_contDiffOn (φ.smooth i)

end SmoothRealFunction
namespace KaehlerMetric

lemma holRealDeriv_comp {φ : Coordinates d → ℝ} {F : ℝ → ℝ} {z : Coordinates d}
    (hφ : DifferentiableAt ℝ φ z) (hF : DifferentiableAt ℝ F (φ z)) :
    holRealDeriv (F ∘ φ) z = fun j => ((deriv F (φ z) : ℝ) : ℂ) * holRealDeriv φ z j := by
  funext j
  unfold holRealDeriv
  rw [(hF.hasDerivAt.comp_hasFDerivAt z hφ.hasFDerivAt).fderiv]
  rw [map_smul]
  rfl

lemma gradientPair_real_smul_left (H : Matrix (Fin d) (Fin d) ℂ)
    (p q : Fin d → ℂ) (a : ℝ) :
    gradientPair H (fun i => (a : ℂ) * p i) q = (a : ℂ) * gradientPair H p q := by
  simp only [gradientPair, star_mul, Complex.star_def, Complex.conj_ofReal, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma energy_comp_left (g : KaehlerMetric A) (ψ φ : SmoothRealFunction A)
    (F : ℝ → ℝ) (hF : ContDiff ℝ ∞ F) (x : X) :
    (g.energy (ψ.compose F hF) φ).value x =
      deriv F (ψ.value x) * (g.energy ψ φ).value x := by
  obtain ⟨i, hi⟩ := A.covers x
  have hz := (A.chart i).mapsTo hi
  have he := g.energy_local (ψ.compose F hF) φ i hz
  have he' := g.energy_local ψ φ i hz
  simp only [SmoothRealFunction.localExpression, Function.comp_apply, (A.chart i).left_inv hi] at he he'
  rw [he, he']
  change (gradientPair _ (holRealDeriv (F ∘ ψ.localExpression i) _) _).re = _
  rw [holRealDeriv_comp (φ := ψ.localExpression i) (((ψ.smooth i).contDiffAt ((A.chart i).open_target.mem_nhds hz)).differentiableAt (by simp))
      (hF.differentiable (by simp) _), gradientPair_real_smul_left]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    SmoothRealFunction.localExpression, Function.comp_apply, (A.chart i).left_inv hi]

lemma energy_comp_self (g : KaehlerMetric A) (φ : SmoothRealFunction A)
    (F : ℝ → ℝ) (hF : ContDiff ℝ ∞ F) (x : X) :
    (g.energy (φ.compose F hF) (φ.compose F hF)).value x =
      (deriv F (φ.value x)) ^ 2 * (g.energy φ φ).value x := by
  rw [g.energy_comp_left, g.energy_symm φ (φ.compose F hF), g.energy_comp_left]
  ring

end KaehlerMetric
end Anticanonical.SourceSmooth

end
end

end OAI
