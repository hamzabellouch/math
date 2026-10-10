import OAI.Analysis.IrrationalRotation.Model.ProductFactorStructure

namespace OAI

noncomputable section
open MeasureTheory
namespace Invariant233.ProductModel

theorem vectorTrace_eq_centralDiagonalIntegral
    (A : Hilbert →L[ℂ] Hilbert) (F : Base → Fiber →L[ℂ] Fiber)
    (hA : ∀ f : Hilbert, A f =ᵐ[baseMeasure] fun x => F x (f x)) :
    vectorTrace traceVector A = centralDiagonalIntegral F := by
  unfold vectorTrace traceVector centralDiagonalIntegral
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_const 2 baseMeasure (lp.single 2 0 (1 : ℂ) : Fiber),
    hA (Lp.const 2 baseMeasure (lp.single 2 0 (1 : ℂ) : Fiber))] with x hx hAx
  rw [hAx, hx]
  rfl

theorem IsCovariantFieldRepresentation.vectorTrace_eq
    {θ : ℕ → ℝ} {A : Hilbert →L[ℂ] Hilbert}
    {F : Base → Fiber →L[ℂ] Fiber} {B : ℝ}
    (h : IsCovariantFieldRepresentation θ A F B) :
    vectorTrace traceVector A = centralDiagonalIntegral F :=
  vectorTrace_eq_centralDiagonalIntegral A F h.2.2.2.1

end Invariant233.ProductModel

end

end OAI
