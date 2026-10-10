import OAI.Analysis.LipschitzHilbert.Fourier.VerticalWindowRescaling
import OAI.Analysis.LipschitzHilbert.Fourier.PartitionedBandFormL1

namespace OAI

noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem finitePartitionedBand_vertical_rescaling_l1 {N : ℕ} {κ : Type} {Label : Fin N → Type} [Fintype κ]
    (psi rho beta : SchwartzMap ℝ ℂ) (H : ℝ) (hH : 0<H)
    (topLength width w : ℝ) (labels : ∀ j, Finset (Label j))
    (theta : ∀ j, labels j → ℝ) (center : κ → ℝ)
    (u : ℝ×ℝ → ℝ) (f : κ → (ℝ×ℝ) → ℂ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) :
    finitePartitionedBandL1 psi rho (verticallyRescaledWindow beta H hH) topLength (H*width) w
      labels theta center u f g=finitePartitionedBandL1 psi rho beta topLength width w
        labels theta center u f g := by
  unfold finitePartitionedBandL1
  simp_rw [verticallyRescaledWindow_symbolY]

end LipschitzHilbert.PacketRepresentation

end

end OAI
