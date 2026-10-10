import OAI.Analysis.LipschitzHilbert.Fourier.LineProductSpectrum
import OAI.Analysis.LipschitzHilbert.Fourier.DyadicCommutatorCutoff

namespace OAI

/-! The actual spectral separation of the low/high dyadic interaction,
and its exact localization by the fixed commutator cutoff. -/
noncomputable section
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem dyadicProjection_frequency (W : ℝ) (hW : 0<W) (f : SchwartzMap ℝ ℂ)
    (eta : ℝ) (heta : (𝓕 (lineSchwartzProjection dyadicDifference W hW.ne' f)) eta≠0) :
    1/W≤|eta| ∧ |eta|≤(13/6)/W := by
  have hn : dyadicDifference (W*eta)≠0 := by
    intro hz
    exact heta (by rw [lineSchwartzProjection_fourier,hz,zero_mul])
  have hlo : 1 < |W*eta| := lt_of_not_ge (fun hh => hn (dyadicDifference_small _ hh))
  have hhi : |W*eta|<13/6 := lt_of_not_ge (fun hh => hn (dyadicDifference_large _ hh))
  rw [abs_mul,abs_of_pos hW] at hlo hhi
  exact ⟨(div_le_iff₀ hW).mpr (by linarith), (le_div_iff₀ hW).mpr (by linarith)⟩

theorem lowpassProjection_frequency (W : ℝ) (hW : 0<W) (f : SchwartzMap ℝ ℂ)
    (eta : ℝ) (heta : (𝓕 (lineSchwartzProjection reassemblyLow W hW.ne' f)) eta≠0) :
    |eta|≤(13/12)/W := by
  have hn : reassemblyLow (W*eta)≠0 := by
    intro hz
    exact heta (by rw [lineSchwartzProjection_fourier,hz,zero_mul])
  have hh : |W*eta|<13/12 := lt_of_not_ge (fun hh => hn (reassemblyLow_zero _ hh))
  rw [abs_mul,abs_of_pos hW] at hh
  exact (le_div_iff₀ hW).mpr (by linarith)

theorem lowHighProduct_frequency (W : ℝ) (hW : 0<W) (b h : SchwartzMap ℝ ℂ) :
    let B := lineSchwartzProjection reassemblyLow (16*W) (by positivity) b
    let H := lineSchwartzProjection dyadicDifference W hW.ne' h
    ∀ eta, (𝓕 (lineSchwartzProduct B H)) eta≠0 → (11/12)/W≤|eta| ∧ |eta|≤(9/4)/W := by
  intro B H eta heta
  have hb := lowpassProjection_frequency (16*W) (by positivity) b
  have hh := dyadicProjection_frequency W hW h
  have hlo := lineSchwartzProduct_annular_lower B H ((13/12)/(16*W)) (1/W) hb
    (fun x hx => (hh x hx).1) eta heta
  have hhi := lineSchwartzProduct_band B H ((13/12)/(16*W)) ((13/6)/W) hb
    (fun x hx => (hh x hx).2) eta heta
  have he1 : 1/W-(13/12)/(16*W)=(179/192)/W := by field_simp [hW.ne']; ring
  have he2 : (13/12)/(16*W)+(13/6)/W=(143/64)/W := by field_simp [hW.ne']; ring
  rw [he1] at hlo
  rw [he2] at hhi
  exact ⟨(div_le_div_of_nonneg_right (by norm_num : (11/12:ℝ)≤179/192) hW.le).trans hlo,
    hhi.trans (div_le_div_of_nonneg_right (by norm_num : (143/64:ℝ)≤9/4) hW.le)⟩

theorem dyadicCommutatorCutoff_absorb (W : ℝ) (hW : 0<W) (f : SchwartzMap ℝ ℂ)
    (hband : ∀ eta, (𝓕 f) eta≠0 → (11/12)/W≤|eta| ∧ |eta|≤(9/4)/W) :
    lineSchwartzProjection dyadicCommutatorCutoff ((2/3)*W) (by positivity) f=f := by
  apply (FourierTransform.fourierEquiv ℂ (SchwartzMap ℝ ℂ)).injective
  ext eta
  change (𝓕 (lineSchwartzProjection dyadicCommutatorCutoff ((2/3)*W) _ f)) eta=(𝓕 f) eta
  rw [lineSchwartzProjection_fourier]
  by_cases hz : (𝓕 f) eta=0
  · rw [hz,mul_zero]
  · have h := hband eta hz
    have hlo : 11/12≤W*|eta| := (div_le_iff₀ hW).mp h.1 |>.trans_eq (by ring)
    have hhi : W*|eta|≤9/4 := by have hh := (le_div_iff₀ hW).mp h.2; nlinarith only [hh]
    have habs : |((2/3)*W)*eta|=(2/3)*(W*|eta|) := by
      rw [abs_mul,abs_of_pos (by positivity : (0:ℝ)<(2/3)*W)]
      ring
    have hp : dyadicCommutatorCutoff (((2/3)*W)*eta)=1 := by
      apply dyadicCommutatorCutoff_one
      rw [habs]
      exact ⟨by linarith,by linarith⟩
    rw [hp,one_mul]

end LipschitzHilbert.PacketRepresentation

end

end OAI
