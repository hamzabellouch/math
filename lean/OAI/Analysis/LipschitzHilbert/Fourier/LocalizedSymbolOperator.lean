import OAI.Analysis.LipschitzHilbert.Fourier.SeparatedSymbolOperator
import OAI.Analysis.LipschitzHilbert.Fourier.LocalizedSymbolIdentity

namespace OAI

/-! The localized symbol is a weighted average of genuine planar
frequency multipliers, with two powers of the weight assigned to the waves. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem planarInverse_const_mul (c : ℂ) (F : ℝ×ℝ → ℂ) (x : ℝ×ℝ) :
    planarInverse (fun omega => c*F omega) x=c*planarInverse F x := by
  simp only [planarInverse, Circle.smul_def, smul_eq_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with omega
  ring

theorem localized_symbol_operator (chi : SchwartzMap ℝ ℝ) (S : SchwartzMap SymbolSpace ℂ)
    (F : ℝ×ℝ → ℂ) (hF : Integrable F planeMeasure)
    (q : ℕ) (l W theta center U : ℝ) (x : ℝ×ℝ) :
    (∫ omega, Real.fourierChar (x.1*omega.1+x.2*omega.2) •
      ((chi U:ℂ)*S (symbolPoint (symbolX l omega.1 omega.2 theta) (symbolY W omega.2 center) U)*F omega)
        ∂planeMeasure) =
      ∫ nu : SymbolSpace, (symbolWeight q nu:ℂ)*localizedSelector chi S q nu U*
        planarInverse (fun omega => (symbolWeight q nu:ℂ)^2*
          modulatedFrequency F nu l W theta center omega) x := by
  calc
    _ = (chi U:ℂ)*(∫ omega, Real.fourierChar (x.1*omega.1+x.2*omega.2) •
        (S (symbolPoint (symbolX l omega.1 omega.2 theta) (symbolY W omega.2 center) U)*F omega)
          ∂planeMeasure) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with omega
      simp only [Circle.smul_def, smul_eq_mul]
      ring
    _ = (chi U:ℂ)*(∫ nu : SymbolSpace, (𝓕 S nu*selectorCharacter nu U)*
        planarInverse (modulatedFrequency F nu l W theta center) x) := by
      rw [separated_symbol_operator S F hF]
    _ = _ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with nu
      rw [planarInverse_const_mul]
      have hw : (symbolWeight q nu:ℂ)≠0 := by
        exact_mod_cast (symbolWeight_pos q nu).ne'
      unfold localizedSelector weightedSelector
      field_simp

end LipschitzHilbert.PacketRepresentation

end

end OAI
