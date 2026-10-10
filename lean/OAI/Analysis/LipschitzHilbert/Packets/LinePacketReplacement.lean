import OAI.Analysis.LipschitzHilbert.Packets.AnalyzedLineMoments

namespace OAI

/-! Replacement synthesis waves retain the already proved analyzing
coefficient budget. This is used for polynomially weighted sums and their
demodulated vertical derivatives. -/

noncomputable section
open MeasureTheory
open scoped FourierTransform

namespace LipschitzHilbert
namespace LinePacketFamily
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

def replaceWaves (P : LinePacketFamily N κ ι) (C : ℝ) (hC : 0 < C)
    (wave : ∀ j, ι j → κ → SchwartzMap ℝ ℂ)
    (hbound : ∀ j i k x, ‖wave j i k x‖ ≤ C *
      (lineEnvelope (P.centerX j i) (P.length j) 3 x *
       lineEnvelope (P.centerZ j i) P.width 2 P.lineY))
    (hderiv : ∀ j i k x, ‖deriv (wave j i k) x‖ ≤ (C / P.length j) *
      (lineEnvelope (P.centerX j i) (P.length j) 3 x *
       lineEnvelope (P.centerZ j i) P.width 2 P.lineY)) : LinePacketFamily N κ ι :=
  { P with
    constant := C
    constant_pos := hC
    wave := wave
    wave_bound := hbound
    deriv_bound := hderiv }

theorem replaceWaves_budget (P : LinePacketFamily N κ ι) (C : ℝ) (hC : 0 < C)
    (wave : ∀ j, ι j → κ → SchwartzMap ℝ ℂ) (hbound hderiv)
    (B : ℝ) (hB : P.HasLocalBudget B) :
    (P.replaceWaves C hC wave hbound hderiv).HasLocalBudget B := hB

end LinePacketFamily
end LipschitzHilbert

end

end OAI
