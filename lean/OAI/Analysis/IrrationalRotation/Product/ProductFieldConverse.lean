import OAI.Analysis.IrrationalRotation.Product.ProductGaugeFourier
import OAI.Analysis.IrrationalRotation.Analysis.StrongFourierRecovery

namespace OAI

noncomputable section
open MeasureTheory

namespace Invariant233.ProductModel

theorem IsCovariantFieldRepresentation.mem_factor
    {θ : ℕ → ℝ} {A : Hilbert →L[ℂ] Hilbert}
    {F : Base → Fiber →L[ℂ] Fiber} {B : ℝ}
    (h : IsCovariantFieldRepresentation θ A F B) : A ∈ factor θ := by
  have hm := StrongFourierRecovery.mem_of_fourier_modes (factor θ)
    (DiagonalGauge.conjugate baseMeasure A)
    (DiagonalGauge.continuous_conjugate_apply baseMeasure A)
    (fun r => h.matrixDiagonal (-r))
    h.matrixDiagonal_neg_apply_integral
    (fun r => h.matrixDiagonal_mem_factor (-r))
  simpa only [DiagonalGauge.conjugate_zero] using hm

theorem mem_factor_iff_covariantFieldRepresentation (θ : ℕ → ℝ)
    (A : Hilbert →L[ℂ] Hilbert) :
    A ∈ factor θ ↔ ∃ (F : Base → Fiber →L[ℂ] Fiber) (B : ℝ),
      IsCovariantFieldRepresentation θ A F B := by
  constructor
  · intro hA
    obtain ⟨F, hF⟩ := exists_covariantFieldRepresentation hA
    exact ⟨F, ‖A‖, hF⟩
  · rintro ⟨F, B, hF⟩
    exact hF.mem_factor

end Invariant233.ProductModel

end

end OAI
