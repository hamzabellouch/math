import OAI.Analysis.LipschitzHilbert.Fourier.SeparatedSymbolPairingL1
import OAI.Analysis.LipschitzHilbert.Packets.UnitPacketSelector

namespace OAI

/-! The separated bilinear form with unit-normalized selectors and the
same two weights already built into the physical wave profiles. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform ComplexConjugate
namespace LipschitzHilbert.PacketRepresentation

theorem unit_symbol_pairing_l1 (chi : SchwartzMap ℝ ℝ) (hchi : ∀ s, |chi s|≤1)
    (C : ℝ) (hC : 0<C) (S : SchwartzMap SymbolSpace ℂ) (q : ℕ)
    (F : ℝ×ℝ → ℂ) (hF : Integrable F planeMeasure) (U : ℝ×ℝ → ℝ) (hU : Measurable U)
    (g : ℝ×ℝ → ℂ) (hgm : Measurable g) (hg : Integrable g planeMeasure)
    (l W theta center : ℝ) :
    (∫ x, (chi (U x):ℂ)*
      (∫ omega, Real.fourierChar (x.1*omega.1+x.2*omega.2) •
        (S (symbolPoint (symbolX l omega.1 omega.2 theta)
          (symbolY W omega.2 center) (U x))*F omega) ∂planeMeasure)*conj (g x)
        ∂planeMeasure) =
    (selectorNormalizer chi C:ℂ)*(∫ nu : SymbolSpace, (symbolWeight q nu:ℂ)*
      ∫ x, unitPacketSelector chi C S q nu (U x)*
        planarInverse (fun omega => (symbolWeight q nu:ℂ)^2*
          modulatedFrequency F nu l W theta center omega) x*conj (g x) ∂planeMeasure) := by
  rw [separated_symbol_pairing_l1 chi hchi S F hF U hU g hgm hg l W theta center,
    ←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with nu
  rw [←integral_const_mul,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [planarInverse_const_mul]
  have hM : (selectorNormalizer chi C:ℂ)≠0 := by
    exact_mod_cast (selectorNormalizer_pos chi C hC).ne'
  have hw : (symbolWeight q nu:ℂ)≠0 := by
    exact_mod_cast (symbolWeight_pos q nu).ne'
  dsimp only [unitPacketSelector,localizedSelector,weightedSelector]
  field_simp

end LipschitzHilbert.PacketRepresentation

end

end OAI
