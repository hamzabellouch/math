import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Angular.AngularHFSmul
import OAI.MeasureTheory.FalconerCompletion.Graphs.AngularMoment

namespace OAI

/-! Angular cutoffs and derivative estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4Near
open Set MeasureTheory
open scoped ComplexConjugate
variable {V : Type*} [MeasurableSpace V]

lemma sourceAngularHFND_smul (d : ℕ) (μ : Measure V) (a v : ℝ)
    (Ψ : ℝ → ℝ) (ψ : V → ℂ) (U W : ℝ × V → ℂ) (lam₁ lam₂ : ℝ) :
    sourceAngularHFND d μ a v Ψ ψ (fun z => lam₁ • U z) (fun z => lam₂ • W z) =
      lam₁^2*lam₂^2*sourceAngularHFND d μ a v Ψ ψ U W := by
  have he (r : ℝ) : (∫ w, ψ w*(lam₁ • U (r,w))*conj (lam₂ • W (r,w)) ∂μ) =
      ((lam₁*lam₂:ℝ):ℂ)*(∫ w, ψ w*U (r,w)*conj (W (r,w)) ∂μ) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with w
    simp only [Complex.real_smul,map_mul,Complex.conj_ofReal,Complex.ofReal_mul]
    ring
  simp only [sourceAngularHFND,he,norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs]
  have he' : (fun r => Ψ (r/(2:ℝ)^v)*((lam₁^2*lam₂^2)*
      ‖∫ w, ψ w*U (r,w)*conj (W (r,w)) ∂μ‖^2)) =
      fun r => (lam₁^2*lam₂^2)*(Ψ (r/(2:ℝ)^v)*‖∫ w, ψ w*U (r,w)*conj (W (r,w)) ∂μ‖^2) := by
    funext r
    ring
  rw [he',integral_const_mul]
  ring

end Attempt4Near
end GraphLiteralSupport
end
end

end OAI
