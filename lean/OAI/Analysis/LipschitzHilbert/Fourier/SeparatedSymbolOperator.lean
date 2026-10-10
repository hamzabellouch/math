import OAI.Analysis.LipschitzHilbert.Fourier.NormalizedSymbolFamily
import OAI.Analysis.LipschitzHilbert.Estimates.FrozenSlopeMultiplier

namespace OAI

/-! Fubini separates the normalized symbol inside the actual planar
frequency integral. The direction parameter is frozen only at its output. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

def modulatedFrequency (F : ℝ×ℝ → ℂ) (nu : SymbolSpace)
    (l W theta center : ℝ) (omega : ℝ×ℝ) : ℂ :=
  frequencyCharacter nu (symbolX l omega.1 omega.2 theta) (symbolY W omega.2 center)*F omega

theorem modulatedFrequency_integrable (F : ℝ×ℝ → ℂ) (hF : Integrable F planeMeasure)
    (nu : SymbolSpace) (l W theta center : ℝ) :
    Integrable (modulatedFrequency F nu l W theta center) planeMeasure := by
  apply hF.norm.mono'
  · apply AEStronglyMeasurable.mul _ hF.aestronglyMeasurable
    exact (show Continuous (fun omega : ℝ×ℝ =>
      frequencyCharacter nu (symbolX l omega.1 omega.2 theta) (symbolY W omega.2 center)) by
        unfold frequencyCharacter symbolX symbolY; fun_prop).aestronglyMeasurable
  · filter_upwards [] with omega
    rw [modulatedFrequency, norm_mul, norm_frequencyCharacter, one_mul]

theorem separated_symbol_operator (S : SchwartzMap SymbolSpace ℂ)
    (F : ℝ×ℝ → ℂ) (hF : Integrable F planeMeasure)
    (l W theta center U : ℝ) (x : ℝ×ℝ) :
    (∫ omega, Real.fourierChar (x.1*omega.1+x.2*omega.2) •
      (S (symbolPoint (symbolX l omega.1 omega.2 theta) (symbolY W omega.2 center) U)*F omega)
        ∂planeMeasure) =
      ∫ nu : SymbolSpace, (𝓕 S nu*selectorCharacter nu U)*
        planarInverse (modulatedFrequency F nu l W theta center) x := by
  let phase := fun (nu : SymbolSpace) (omega : ℝ×ℝ) =>
    frequencyCharacter nu (symbolX l omega.1 omega.2 theta) (symbolY W omega.2 center)*
      selectorCharacter nu U*(Real.fourierChar (x.1*omega.1+x.2*omega.2):ℂ)
  let H := fun p : SymbolSpace×(ℝ×ℝ) => (𝓕 S p.1*F p.2)*phase p.1 p.2
  have hH : Integrable H (volume.prod planeMeasure) := by
    apply ((𝓕 S : SchwartzMap SymbolSpace ℂ).integrable.mul_prod hF).mul_bdd (c := 1)
    · exact (show Continuous (fun p : SymbolSpace×(ℝ×ℝ) => phase p.1 p.2) by
        unfold phase frequencyCharacter selectorCharacter symbolX symbolY; fun_prop).aestronglyMeasurable
    · filter_upwards [] with p
      dsimp only [phase]
      rw [norm_mul, norm_mul, norm_frequencyCharacter, norm_selectorCharacter, Circle.norm_coe]
      norm_num
  have hleft (omega : ℝ×ℝ) :
      Real.fourierChar (x.1*omega.1+x.2*omega.2) •
        (S (symbolPoint (symbolX l omega.1 omega.2 theta) (symbolY W omega.2 center) U)*F omega)=
          ∫ nu : SymbolSpace, H (nu,omega) := by
    rw [separated_symbol_fourier]
    simp only [Circle.smul_def, smul_eq_mul]
    rw [← integral_mul_const, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with nu
    dsimp only [H,phase]
    ring
  have hright (nu : SymbolSpace) : (∫ omega, H (nu,omega) ∂planeMeasure)=
      (𝓕 S nu*selectorCharacter nu U)*
        planarInverse (modulatedFrequency F nu l W theta center) x := by
    rw [planarInverse, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with omega
    simp only [H,phase,modulatedFrequency,Circle.smul_def,smul_eq_mul]
    ring
  calc
    _ = ∫ omega, (∫ nu : SymbolSpace, H (nu,omega)) ∂planeMeasure :=
      integral_congr_ae (Filter.Eventually.of_forall hleft)
    _ = ∫ nu : SymbolSpace, ∫ omega, H (nu,omega) ∂planeMeasure :=
      (integral_integral_swap hH).symm
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall hright)

end LipschitzHilbert.PacketRepresentation

end

end OAI
