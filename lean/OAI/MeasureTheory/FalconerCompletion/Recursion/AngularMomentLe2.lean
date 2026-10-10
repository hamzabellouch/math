import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Graphs.AngularMoment
import OAI.MeasureTheory.FalconerCompletion.Recursion.AngularMomentLe

namespace OAI

/-! Recursive policies and quantitative depth estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4Near
open Set MeasureTheory
open scoped ComplexConjugate
variable {V : Type*} [MeasurableSpace V]

lemma sourceAngularMomentND_le (μ : Measure V) [IsFiniteMeasure μ]
    {U W : ℝ × V → ℂ} (hW : Measurable W) {C : ℝ}
    (hb : ∀ r, ∀ᵐ w ∂μ, ‖W (r,w)‖ ≤ C) (r : ℝ)
    (hUW : ∀ᵐ w ∂μ, ‖U (r,w)‖ ≤ ‖W (r,w)‖) :
    sourceAngularMomentND μ U r ≤ sourceAngularMomentND μ W r := by
  apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
    (angular_square_integrableND μ (hW.comp (measurable_const.prodMk measurable_id)) (hb r))
  filter_upwards [hUW] with w hw
  exact pow_le_pow_left₀ (norm_nonneg _) hw 2

lemma sourceAngularMomentND_cutoff_le (μ : Measure V) [IsFiniteMeasure μ]
    {U : ℝ × V → ℂ} (hU : Measurable U) {C : ℝ}
    (hb : ∀ r, ∀ᵐ w ∂μ, ‖U (r,w)‖ ≤ C) (ψ : V → ℂ)
    (hψ : ∀ᵐ w ∂μ, ‖ψ w‖ ≤ 1) (r : ℝ) :
    sourceAngularMomentND μ (fun z => ψ z.2*U z) r ≤ sourceAngularMomentND μ U r := by
  apply sourceAngularMomentND_le μ hU hb
  filter_upwards [hψ] with w hw
  simpa only [norm_mul,one_mul] using mul_le_mul_of_nonneg_right hw (norm_nonneg (U (r,w)))

lemma sourceAngularMomentND_smul (μ : Measure V) (lam : ℝ) (U : ℝ × V → ℂ) (r : ℝ) :
    sourceAngularMomentND μ (fun z => lam • U z) r = lam^2*sourceAngularMomentND μ U r := by
  simp only [sourceAngularMomentND,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,integral_const_mul]

lemma sourceAngularHND_nonneg (d : ℕ) (μ : Measure V) (a v : ℝ)
    {Ψ : ℝ → ℝ} (hΨ : ∀ r, 0 ≤ Ψ r) (U W : ℝ × V → ℂ) :
    0 ≤ sourceAngularHND d μ a v Ψ U W := by
  apply mul_nonneg (by positivity)
  exact integral_nonneg (fun r => mul_nonneg
    (mul_nonneg (hΨ _) (sourceAngularMomentND_nonneg μ U r)) (sourceAngularMomentND_nonneg μ W r))

lemma sourceAngularHFND_nonneg (d : ℕ) (μ : Measure V) (a v : ℝ)
    {Ψ : ℝ → ℝ} (hΨ : ∀ r, 0 ≤ Ψ r) (ψ : V → ℂ) (U W : ℝ × V → ℂ) :
    0 ≤ sourceAngularHFND d μ a v Ψ ψ U W := by
  apply mul_nonneg (by positivity)
  exact integral_nonneg (fun r => mul_nonneg (hΨ _) (sq_nonneg _))

lemma sourceAngularHND_smul (d : ℕ) (μ : Measure V) (a v : ℝ)
    (Ψ : ℝ → ℝ) (U W : ℝ × V → ℂ) (lam₁ lam₂ : ℝ) :
    sourceAngularHND d μ a v Ψ (fun z => lam₁ • U z) (fun z => lam₂ • W z) =
      lam₁^2*lam₂^2*sourceAngularHND d μ a v Ψ U W := by
  simp only [sourceAngularHND,sourceAngularMomentND_smul]
  have he : (fun r => Ψ (r/(2:ℝ)^v)*(lam₁^2*sourceAngularMomentND μ U r)*
      (lam₂^2*sourceAngularMomentND μ W r)) =
      fun r => (lam₁^2*lam₂^2)*(Ψ (r/(2:ℝ)^v)*sourceAngularMomentND μ U r*sourceAngularMomentND μ W r) := by
    funext r
    ring
  rw [he,integral_const_mul]
  ring

lemma sourceAngularHND_depth (d : ℕ) (μ : Measure V) (a p v : ℝ)
    (Ψ : ℝ → ℝ) (U W : ℝ × V → ℂ) :
    sourceAngularHND d μ a v Ψ U W =
      (2:ℝ)^((d:ℝ)*(p-a))*sourceAngularHND d μ p v Ψ U W := by
  dsimp [sourceAngularHND]
  rw [← mul_assoc,← mul_assoc,← Real.rpow_add (by norm_num : (0:ℝ)<2)]
  congr 3
  ring

lemma sourceAngularHFND_cutoff (d : ℕ) (μ : Measure V) (a v : ℝ)
    (Ψ : ℝ → ℝ) (ψ : V → ℂ) (U W : ℝ × V → ℂ) :
    sourceAngularHFND d μ a v Ψ ψ U W =
      sourceAngularHFND d μ a v Ψ (fun _ => 1) (fun z => ψ z.2*U z) W := by
  simp [sourceAngularHFND]

end Attempt4Near
end GraphLiteralSupport
end
end

end OAI
