import Mathlib
import OAI.Geometry.PrescribedRicci.GlobalKahlerEnergy
import OAI.Geometry.PrescribedRicci.KahlerEnergyChain

namespace OAI

/-! Kahler Energy Product. -/

section

 
noncomputable section
open Matrix Set Filter Topology MeasureTheory
open scoped ContDiff ComplexOrder Classical
namespace Anticanonical.SourceSmooth.KaehlerMetric
variable {d : ℕ}

lemma gradientPair_add_right (H : Matrix (Fin d) (Fin d) ℂ) (p q r : Fin d → ℂ) :
    gradientPair H p (q+r) = gradientPair H p q + gradientPair H p r := by
  simp [gradientPair, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma gradientPair_real_smul_right (H : Matrix (Fin d) (Fin d) ℂ)
    (p q : Fin d → ℂ) (a : ℝ) :
    gradientPair H p (fun i => (a : ℂ)*q i) = (a : ℂ)*gradientPair H p q := by
  simp only [gradientPair, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma gradientPair_smul_self (H : Matrix (Fin d) (Fin d) ℂ) (p : Fin d → ℂ) (a : ℝ) :
    (gradientPair H (fun i => (a:ℂ)*p i) (fun i => (a:ℂ)*p i)).re =
      a^2 * (gradientPair H p p).re := by
  rw [gradientPair_real_smul_left, gradientPair_real_smul_right]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

lemma gradientPair_add_self_le (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.PosDef)
    (p q : Fin d → ℂ) :
    (gradientPair H (p+q) (p+q)).re ≤
      2 * (gradientPair H p p).re + 2 * (gradientPair H q q).re := by
  have hh := gradientPair_self_nonneg H hH (p + fun i => ((-1:ℝ):ℂ)*q i)
  simp only [gradientPair_add_left, gradientPair_add_right,
    gradientPair_real_smul_left, gradientPair_real_smul_right,
    Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at hh ⊢
  nlinarith

variable {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}
lemma energy_product_le (g : KaehlerMetric A) (ψ φ : SmoothRealFunction A) (x : X) :
    (g.energy (ψ.product φ) (ψ.product φ)).value x ≤
      2 * ψ.value x ^ 2 * (g.energy φ φ).value x +
      2 * φ.value x ^ 2 * (g.energy ψ ψ).value x := by
  obtain ⟨i,hi⟩ := A.covers x
  have hz := (A.chart i).mapsTo hi
  have he := g.energy_local (ψ.product φ) (ψ.product φ) i hz
  have heψ := g.energy_local ψ ψ i hz
  have heφ := g.energy_local φ φ i hz
  simp only [SmoothRealFunction.localExpression, Function.comp_apply,
    (A.chart i).left_inv hi] at he heψ heφ
  rw [he,heψ,heφ]
  have hd : holRealDeriv ((ψ.product φ).localExpression i) ((A.chart i) x) =
      (fun j => (ψ.value x : ℂ) * holRealDeriv (φ.localExpression i) ((A.chart i) x) j) +
      (fun j => (φ.value x : ℂ) * holRealDeriv (ψ.localExpression i) ((A.chart i) x) j) := by
    funext j
    change holRealDeriv (fun y => ψ.localExpression i y * φ.localExpression i y) _ j = _
    rw [holRealDeriv_mul (φ := ψ.localExpression i) (ψ := φ.localExpression i) (((ψ.smooth i).contDiffAt ((A.chart i).open_target.mem_nhds hz)).differentiableAt (by simp))
      (((φ.smooth i).contDiffAt ((A.chart i).open_target.mem_nhds hz)).differentiableAt (by simp))]
    simp only [SmoothRealFunction.localExpression, Function.comp_apply,
      (A.chart i).left_inv hi, Pi.add_apply]
  change (gradientPair _ (holRealDeriv ((ψ.product φ).localExpression i) _)
    (holRealDeriv ((ψ.product φ).localExpression i) _)).re ≤ _
  rw [hd]
  have hh := gradientPair_add_self_le _ (g.positive i _ hz)
    (fun j => (ψ.value x : ℂ)*holRealDeriv (φ.localExpression i) ((A.chart i) x) j)
    (fun j => (φ.value x : ℂ)*holRealDeriv (ψ.localExpression i) ((A.chart i) x) j)
  rw [gradientPair_smul_self,gradientPair_smul_self] at hh
  simpa only [mul_assoc, SmoothRealFunction.localExpression] using hh

end Anticanonical.SourceSmooth.KaehlerMetric

end
end

end OAI
