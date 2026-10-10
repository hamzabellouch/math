import OAI.Analysis.LipschitzHilbert.Packets.FactoredMultiplierPackets
import OAI.Analysis.LipschitzHilbert.Phase.PlanarSliceFourierAngular

namespace OAI

/-! Translation, reflection, and conjugation for the actual convolution
packets. The analyzing packet retains the original positive-frequency
support; reflection and conjugation cancel their frequency reversals. -/
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
namespace LipschitzHilbert.PacketRepresentation

theorem synthesisWave_fourier (area : ℝ) (K : ℝ×ℝ → ℂ) (z : ℝ×ℝ) (xi eta : ℝ) :
    planarAngularFourier (synthesisWave area K z) (xi,eta)=
      (area:ℂ)*Complex.exp (-(Complex.I*((z.1:ℂ)*xi+(z.2:ℂ)*eta)))*
        planarAngularFourier K (xi,eta) := by
  rw [planarAngularFourier_eq_integral, planarAngularFourier_eq_integral]
  let H := fun y : ℝ×ℝ => Complex.exp (-(Complex.I*((y.1:ℂ)*xi+(y.2:ℂ)*eta)))*
    synthesisWave area K z y
  have ht := integral_add_right_eq_self (μ := planeMeasure) H z
  change (∫ y, H y ∂planeMeasure)=_
  rw [← ht, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  dsimp [H,synthesisWave]
  simp only [add_sub_cancel_right, Complex.ofReal_add]
  rw [show -(Complex.I*(((y.1:ℂ)+(z.1:ℂ))*xi+((y.2:ℂ)+(z.2:ℂ))*eta))=
      -(Complex.I*((z.1:ℂ)*xi+(z.2:ℂ)*eta))+
        -(Complex.I*((y.1:ℂ)*xi+(y.2:ℂ)*eta)) by ring, Complex.exp_add]
  ring

theorem analyzingWave_fourier (area : ℝ) (K : ℝ×ℝ → ℂ) (z : ℝ×ℝ) (xi eta : ℝ) :
    planarAngularFourier (analyzingWave area K z) (xi,eta)=
      (area:ℂ)*Complex.exp (-(Complex.I*((z.1:ℂ)*xi+(z.2:ℂ)*eta)))*
        conj (planarAngularFourier K (xi,eta)) := by
  rw [planarAngularFourier_eq_integral, planarAngularFourier_eq_integral]
  let H := fun y : ℝ×ℝ => Complex.exp (-(Complex.I*((y.1:ℂ)*xi+(y.2:ℂ)*eta)))*
    analyzingWave area K z y
  have ht := integral_sub_left_eq_self (μ := planeMeasure) H z
  change (∫ y, H y ∂planeMeasure)=_
  rw [← ht, ← integral_conj, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  dsimp [H,analyzingWave]
  simp only [sub_sub_cancel, Complex.ofReal_sub, map_mul]
  rw [← Complex.exp_conj]
  simp only [map_neg, map_mul, map_add, Complex.conj_I, Complex.conj_ofReal]
  rw [show -(Complex.I*(((z.1:ℂ)-(y.1:ℂ))*xi+((z.2:ℂ)-(y.2:ℂ))*eta))=
      -(Complex.I*((z.1:ℂ)*xi+(z.2:ℂ)*eta))+
        -((-Complex.I)*((y.1:ℂ)*xi+(y.2:ℂ)*eta)) by ring, Complex.exp_add]
  ring

theorem synthesisWave_spectrum {S : Set (ℝ×ℝ)} (area : ℝ) (K : ℝ×ℝ → ℂ)
    (hK : ∀ omega, planarAngularFourier K omega≠0 → omega∈S)
    (z : ℝ×ℝ) (omega : ℝ×ℝ)
    (h : planarAngularFourier (synthesisWave area K z) omega≠0) : omega∈S := by
  apply hK omega
  intro hz
  rcases omega with ⟨xi,eta⟩
  rw [synthesisWave_fourier, hz, mul_zero] at h
  exact h rfl

theorem analyzingWave_spectrum {S : Set (ℝ×ℝ)} (area : ℝ) (K : ℝ×ℝ → ℂ)
    (hK : ∀ omega, planarAngularFourier K omega≠0 → omega∈S)
    (z : ℝ×ℝ) (omega : ℝ×ℝ)
    (h : planarAngularFourier (analyzingWave area K z) omega≠0) : omega∈S := by
  apply hK omega
  intro hz
  rcases omega with ⟨xi,eta⟩
  rw [analyzingWave_fourier, hz, map_zero, mul_zero] at h
  exact h rfl

end LipschitzHilbert.PacketRepresentation

end

end OAI
