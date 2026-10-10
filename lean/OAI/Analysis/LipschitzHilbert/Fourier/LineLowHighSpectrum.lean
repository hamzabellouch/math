import OAI.Analysis.LipschitzHilbert.Fourier.LineLowHighCommutator

namespace OAI

/-! The low/high commutator output stays in a fixed annulus. -/
noncomputable section
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem lineSchwartzProjection_comm (q p : SchwartzMap ℝ ℂ)
    (W V : ℝ) (hW : W≠0) (hV : V≠0) (f : SchwartzMap ℝ ℂ) :
    lineSchwartzProjection q W hW (lineSchwartzProjection p V hV f)=
      lineSchwartzProjection p V hV (lineSchwartzProjection q W hW f) := by
  apply (FourierTransform.fourierEquiv ℂ (SchwartzMap ℝ ℂ)).injective
  ext eta
  change (𝓕 (lineSchwartzProjection q W hW (lineSchwartzProjection p V hV f))) eta=
    (𝓕 (lineSchwartzProjection p V hV (lineSchwartzProjection q W hW f))) eta
  simp only [lineSchwartzProjection_fourier]
  ring

theorem lowHighCommutator_frequency (m b h : SchwartzMap ℝ ℂ) (W : ℝ) (hW : 0<W) :
    let B := lineSchwartzProjection reassemblyLow (16*W) (by positivity) b
    let H := lineSchwartzProjection dyadicDifference W hW.ne' h
    ∀ eta, (𝓕 (lineSchwartzCommutator m B (schwartzDerivative 1 H))) eta≠0 →
      (11/12)/W≤|eta| ∧ |eta|≤(9/4)/W := by
  intro B H eta heta
  have hD : schwartzDerivative 1 H=lineSchwartzProjection dyadicDifference W hW.ne' (schwartzDerivative 1 h) :=
    lineSchwartzProjection_derivative dyadicDifference W hW.ne' h
  have hcomm : lineSchwartzProjection m 1 (by norm_num) (schwartzDerivative 1 H)=
      lineSchwartzProjection dyadicDifference W hW.ne'
        (lineSchwartzProjection m 1 (by norm_num) (schwartzDerivative 1 h)) := by
    rw [hD]
    exact lineSchwartzProjection_comm m dyadicDifference 1 W (by norm_num) hW.ne' _
  have hfirst : ∀ eta, (𝓕 (lineSchwartzProduct B
      (lineSchwartzProjection m 1 (by norm_num) (schwartzDerivative 1 H)))) eta≠0 →
      (11/12)/W≤|eta| ∧ |eta|≤(9/4)/W := by
    rw [hcomm]
    exact lowHighProduct_frequency W hW b (lineSchwartzProjection m 1 (by norm_num) (schwartzDerivative 1 h))
  have hsecond : ∀ eta, (𝓕 (lineSchwartzProduct B (schwartzDerivative 1 H))) eta≠0 →
      (11/12)/W≤|eta| ∧ |eta|≤(9/4)/W := by
    rw [hD]
    exact lowHighProduct_frequency W hW b (schwartzDerivative 1 h)
  have he : (𝓕 (lineSchwartzCommutator m B (schwartzDerivative 1 H))) eta=
      (𝓕 (lineSchwartzProduct B (lineSchwartzProjection m 1 (by norm_num) (schwartzDerivative 1 H)))) eta-
      m eta*(𝓕 (lineSchwartzProduct B (schwartzDerivative 1 H))) eta := by
    change (FourierTransform.fourierCLM ℂ (SchwartzMap ℝ ℂ)
      (lineSchwartzProduct B (lineSchwartzProjection m 1 (by norm_num) (schwartzDerivative 1 H))-
        lineSchwartzProjection m 1 (by norm_num) (lineSchwartzProduct B (schwartzDerivative 1 H)))) eta=_
    rw [map_sub,sub_apply,FourierTransform.fourierCLM_apply,FourierTransform.fourierCLM_apply,
      lineSchwartzProjection_fourier,one_mul]
  by_cases hf : (𝓕 (lineSchwartzProduct B
      (lineSchwartzProjection m 1 (by norm_num) (schwartzDerivative 1 H)))) eta=0
  · apply hsecond eta
    intro hs
    apply heta
    rw [he,hf,hs,mul_zero,sub_zero]
  · exact hfirst eta hf

end LipschitzHilbert.PacketRepresentation

end

end OAI
