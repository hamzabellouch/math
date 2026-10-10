import OAI.Analysis.LipschitzHilbert.Fourier.ModulatedInverse

namespace OAI

/-! Joint parameter continuity of the inverse modulated multiplier only
needs integrable frequency data, so it applies to amplitude slices. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem modulated_inverse_joint_continuous_l1 (F : ℝ×ℝ → ℂ)
    (hF : Integrable F planeMeasure) (l W theta center : ℝ) :
    Continuous (fun p : SymbolSpace×(ℝ×ℝ) =>
      planarInverse (modulatedFrequency F p.1 l W theta center) p.2) := by
  unfold planarInverse modulatedFrequency
  apply continuous_of_dominated (bound:=fun omega => ‖F omega‖)
  · intro p
    have hp : Continuous (fun omega : ℝ×ℝ =>
        (Real.fourierChar (p.2.1*omega.1+p.2.2*omega.2):ℂ)*
          frequencyCharacter p.1 (symbolX l omega.1 omega.2 theta) (symbolY W omega.2 center)) := by
      unfold frequencyCharacter symbolX symbolY
      fun_prop
    apply (hp.aestronglyMeasurable.mul hF.aestronglyMeasurable).congr
    filter_upwards [] with omega
    change ((Real.fourierChar (p.2.1*omega.1+p.2.2*omega.2):ℂ)*
      frequencyCharacter p.1 (symbolX l omega.1 omega.2 theta) (symbolY W omega.2 center))*F omega=
      (Real.fourierChar (p.2.1*omega.1+p.2.2*omega.2):ℂ)*
        (frequencyCharacter p.1 (symbolX l omega.1 omega.2 theta) (symbolY W omega.2 center)*F omega)
    ring
  · intro p
    filter_upwards [] with omega
    simp only [Circle.norm_smul,norm_mul,norm_frequencyCharacter,one_mul,le_refl]
  · exact hF.norm
  · filter_upwards [] with omega
    unfold frequencyCharacter symbolX symbolY
    fun_prop

end LipschitzHilbert.PacketRepresentation

end

end OAI
