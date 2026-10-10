import OAI.Analysis.LipschitzHilbert.Fourier.LineHighLowEnergy

namespace OAI

/-! A gap of five binary scales puts every high/low output in the
same fixed annulus as the high coefficient. -/
noncomputable section
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem lineSchwartzProduct_comm (f g : SchwartzMap ℝ ℂ) :
    lineSchwartzProduct f g=lineSchwartzProduct g f := by
  ext x
  simp only [lineSchwartzProduct_apply,mul_comm]

theorem lineSchwartzProjection_frequency_of_nonzero (q f : SchwartzMap ℝ ℂ)
    (W : ℝ) (hW : W≠0) (eta : ℝ)
    (heta : (𝓕 (lineSchwartzProjection q W hW f) : SchwartzMap ℝ ℂ) eta≠0) :
    (𝓕 f : SchwartzMap ℝ ℂ) eta≠0 := by
  intro hz
  exact heta (by rw [lineSchwartzProjection_fourier,hz,mul_zero])

theorem schwartzDerivative_frequency_of_nonzero (f : SchwartzMap ℝ ℂ) (eta : ℝ)
    (heta : (𝓕 (schwartzDerivative 1 f) : SchwartzMap ℝ ℂ) eta≠0) :
    (𝓕 f : SchwartzMap ℝ ℂ) eta≠0 := by
  intro hz
  exact heta (by rw [fourier_schwartzDerivative,hz,mul_zero])

theorem highLowProduct_frequency (B H : SchwartzMap ℝ ℂ) (W V : ℝ)
    (hW : 0<W) (hgap : 32*W≤V)
    (hB : ∀ eta, (𝓕 B : SchwartzMap ℝ ℂ) eta≠0 → 1/W≤|eta| ∧ |eta|≤(13/6)/W)
    (hH : ∀ eta, (𝓕 H : SchwartzMap ℝ ℂ) eta≠0 → |eta|≤(13/6)/V) :
    ∀ eta, (𝓕 (lineSchwartzProduct B H) : SchwartzMap ℝ ℂ) eta≠0 →
      (11/12)/W≤|eta| ∧ |eta|≤(9/4)/W := by
  have hV : 0<V := lt_of_lt_of_le (by positivity) hgap
  have hR : (13/6)/V≤(1/12)/W := by
    apply (div_le_div_iff₀ hV hW).mpr
    nlinarith
  intro eta heta
  have hhi := lineSchwartzProduct_band B H ((13/6)/W) ((13/6)/V)
    (fun x hx => (hB x hx).2) hH eta heta
  have hlo := lineSchwartzProduct_annular_lower H B ((13/6)/V) (1/W)
    hH (fun x hx => (hB x hx).1) eta (by rwa [lineSchwartzProduct_comm H B])
  constructor
  · have he : (11/12)/W=1/W-(1/12)/W := by ring
    rw [he]; linarith
  · have he : (9/4)/W=(13/6)/W+(1/12)/W := by ring
    rw [he]; linarith

theorem highLowCommutator_frequency (m b h : SchwartzMap ℝ ℂ) (W V : ℝ)
    (hW : 0<W) (hV : 0<V) (hgap : 32*W≤V) :
    let B := lineSchwartzProjection dyadicDifference W hW.ne' b
    let H := lineSchwartzProjection dyadicDifference V hV.ne' h
    ∀ eta, (𝓕 (lineSchwartzCommutator m B (schwartzDerivative 1 H)) : SchwartzMap ℝ ℂ) eta≠0 →
      (11/12)/W≤|eta| ∧ |eta|≤(9/4)/W := by
  intro B H eta heta
  have hb := dyadicProjection_frequency W hW b
  have hh : ∀ x, (𝓕 (schwartzDerivative 1 H) : SchwartzMap ℝ ℂ) x≠0 → |x|≤(13/6)/V := by
    intro x hx
    exact (dyadicProjection_frequency V hV h x (schwartzDerivative_frequency_of_nonzero H x hx)).2
  have ht : ∀ x, (𝓕 (lineSchwartzProjection m 1 (by norm_num) (schwartzDerivative 1 H)) : SchwartzMap ℝ ℂ) x≠0 → |x|≤(13/6)/V := by
    intro x hx
    exact hh x (lineSchwartzProjection_frequency_of_nonzero m _ 1 (by norm_num) x hx)
  have hfirst := highLowProduct_frequency B (lineSchwartzProjection m 1 (by norm_num) (schwartzDerivative 1 H)) W V hW hgap hb ht
  have hsecond := highLowProduct_frequency B (schwartzDerivative 1 H) W V hW hgap hb hh
  have he : (𝓕 (lineSchwartzCommutator m B (schwartzDerivative 1 H)) : SchwartzMap ℝ ℂ) eta=
      (𝓕 (lineSchwartzProduct B (lineSchwartzProjection m 1 (by norm_num) (schwartzDerivative 1 H))) : SchwartzMap ℝ ℂ) eta-
        m eta*(𝓕 (lineSchwartzProduct B (schwartzDerivative 1 H)) : SchwartzMap ℝ ℂ) eta := by
    change (FourierTransform.fourierCLM ℂ (SchwartzMap ℝ ℂ)
      (lineSchwartzProduct B (lineSchwartzProjection m 1 (by norm_num) (schwartzDerivative 1 H))-
        lineSchwartzProjection m 1 (by norm_num) (lineSchwartzProduct B (schwartzDerivative 1 H)))) eta=_
    rw [map_sub,sub_apply,FourierTransform.fourierCLM_apply,FourierTransform.fourierCLM_apply,
      lineSchwartzProjection_fourier,one_mul]
  by_cases hf : (𝓕 (lineSchwartzProduct B (lineSchwartzProjection m 1 (by norm_num) (schwartzDerivative 1 H))) : SchwartzMap ℝ ℂ) eta=0
  · apply hsecond eta
    intro hs
    exact heta (by rw [he,hf,hs,mul_zero,sub_zero])
  · exact hfirst eta hf

end LipschitzHilbert.PacketRepresentation

end

end OAI
