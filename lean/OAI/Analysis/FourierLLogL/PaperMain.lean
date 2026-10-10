import OAI.Analysis.FourierLLogL.Main

open MeasureTheory Filter
open scoped BigOperators Topology

namespace OAI.FourierLLogL

theorem paperMain (f : AddCircle (2 * Real.pi) → ℂ)
    (hfm : AEStronglyMeasurable f AddCircle.haarAddCircle)
    (hfi : Integrable (fun x ↦ ‖f x‖ * Real.log (2 + ‖f x‖))
      AddCircle.haarAddCircle) :
    ∃ E : Set (AddCircle (2 * Real.pi)),
      MeasurableSet E ∧ AddCircle.haarAddCircle E = 0 ∧ ∀ x ∉ E,
        Tendsto
          (fun N : ℕ ↦
            ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), fourierCoeff f k * fourier k x)
          atTop (𝓝 (f x)) := by
  simpa only [circleMeasure, symmetricPartialSum] using
    (almost_everywhere_fourier_convergence f ⟨hfm, hfi⟩)

end OAI.FourierLLogL
