import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Graphs.GraphDegrees
import OAI.MeasureTheory.FalconerCompletion.Graphs.GraphJetMul

namespace OAI

/-! Angular cutoffs and derivative estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace Attempt4Near
open MeasureTheory
open scoped ComplexConjugate
variable {V : Type*} [MeasurableSpace V]

lemma sourceAngularHND_congr (d : ℕ) (μ : Measure V) (a v : ℝ) (Ψ : ℝ → ℝ)
    {U U' W W' : ℝ×V → ℂ}
    (hU : ∀ r, ∀ᵐ w ∂μ, U (r,w)=U' (r,w))
    (hW : ∀ r, ∀ᵐ w ∂μ, W (r,w)=W' (r,w)) :
    sourceAngularHND d μ a v Ψ U W = sourceAngularHND d μ a v Ψ U' W' := by
  unfold sourceAngularHND
  congr 1
  apply integral_congr_ae
  filter_upwards with r
  have hu : sourceAngularMomentND μ U r = sourceAngularMomentND μ U' r :=
    integral_congr_ae ((hU r).mono (fun _ h => by dsimp only; rw [h]))
  have hw : sourceAngularMomentND μ W r = sourceAngularMomentND μ W' r :=
    integral_congr_ae ((hW r).mono (fun _ h => by dsimp only; rw [h]))
  rw [hu,hw]

lemma sourceAngularHFND_congr (d : ℕ) (μ : Measure V) (a v : ℝ) (Ψ : ℝ → ℝ) (ψ : V → ℂ)
    {U U' W W' : ℝ×V → ℂ}
    (hU : ∀ r, ∀ᵐ w ∂μ, U (r,w)=U' (r,w))
    (hW : ∀ r, ∀ᵐ w ∂μ, W (r,w)=W' (r,w)) :
    sourceAngularHFND d μ a v Ψ ψ U W = sourceAngularHFND d μ a v Ψ ψ U' W' := by
  unfold sourceAngularHFND
  congr 1
  apply integral_congr_ae
  filter_upwards with r
  have h : (∫ w, ψ w*U (r,w)*conj (W (r,w)) ∂μ) =
      ∫ w, ψ w*U' (r,w)*conj (W' (r,w)) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hU r,hW r] with w hu hw
    rw [hu,hw]
  rw [h]
end Attempt4Near
end
end

end OAI
