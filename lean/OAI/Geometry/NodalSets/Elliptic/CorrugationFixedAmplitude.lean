import OAI.Geometry.NodalSets.Elliptic.CorrugationWellChoice

namespace OAI

namespace Yau.Geometry
open Set
noncomputable section

def corrugationFixedAmplitude : ℝ := Classical.choose exists_fixed_corrugation_slope

lemma corrugationFixedAmplitude_spec :
    0 < corrugationFixedAmplitude ∧ corrugationFixedAmplitude ≤ 1 ∧
    (∀ r : ℝ, 0 ≤ r → corrugationSlope corrugationFixedAmplitude (1/4) r *
      max (-deriv (corrugationSlope corrugationFixedAmplitude (1/4)) r) 0 ≤ 1/(64*(1/4:ℝ))) ∧
    ∃ l₀ : ℝ, 0 < l₀ ∧ ∀ r ∈ Icc (1/16:ℝ) (1/8),
      l₀ ≤ corrugationSlope corrugationFixedAmplitude (1/4) r := by
  obtain ⟨C,l₀,ha,ha1,_,hl₀,_,hb,hann,_⟩ := Classical.choose_spec exists_fixed_corrugation_slope
  exact ⟨ha,ha1,fun r hr ↦ (hb r hr).2.2.2,l₀,hl₀,hann⟩

end
end Yau.Geometry

end OAI
