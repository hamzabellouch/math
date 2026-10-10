import OAI.Analysis.LipschitzHilbert.Fourier.LineFrequencyProjection

namespace OAI

/-! The Fourier spectrum of an actual Schwartz product, including the
ball and annulus bounds needed in the dyadic commutator decomposition. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

def lineSchwartzProduct (f g : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) f g

@[simp] theorem lineSchwartzProduct_apply (f g : SchwartzMap ℝ ℂ) (x : ℝ) :
    lineSchwartzProduct f g x=f x*g x := by
  simp only [lineSchwartzProduct,SchwartzMap.pairing_apply_apply,ContinuousLinearMap.mul_apply']

theorem schwartz_fourier_twice (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    (𝓕 (𝓕 f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ) x=f (-x) := by
  have he : (𝓕⁻ (𝓕 f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ)=f := FourierTransform.fourierInv_fourier_eq f
  have hh := congrArg (fun g : SchwartzMap ℝ ℂ => g (-x)) he
  change (𝓕 (𝓕 f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ) (-(-x))=f (-x) at hh
  simpa only [neg_neg] using hh

theorem lineSchwartzProduct_fourier (f g : SchwartzMap ℝ ℂ) :
    (𝓕 (lineSchwartzProduct f g) : SchwartzMap ℝ ℂ)=
      SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (𝓕 f) (𝓕 g) := by
  apply (FourierTransform.fourierEquiv ℂ (SchwartzMap ℝ ℂ)).symm.injective
  change 𝓕⁻ (𝓕 (lineSchwartzProduct f g) : SchwartzMap ℝ ℂ)=
    𝓕⁻ (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (𝓕 f) (𝓕 g))
  rw [FourierTransform.fourierInv_fourier_eq]
  ext x
  change lineSchwartzProduct f g x=
    (𝓕 (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (𝓕 f) (𝓕 g)) : SchwartzMap ℝ ℂ) (-x)
  rw [SchwartzMap.fourier_convolution]
  simp only [SchwartzMap.pairing_apply_apply,ContinuousLinearMap.mul_apply',schwartz_fourier_twice,
    neg_neg,lineSchwartzProduct_apply]

theorem lineSchwartzProduct_fourier_zero (f g : SchwartzMap ℝ ℂ) (eta : ℝ)
    (h : ∀ t, (𝓕 f : SchwartzMap ℝ ℂ) t=0 ∨ (𝓕 g : SchwartzMap ℝ ℂ) (eta-t)=0) :
    (𝓕 (lineSchwartzProduct f g) : SchwartzMap ℝ ℂ) eta=0 := by
  rw [lineSchwartzProduct_fourier,SchwartzMap.convolution_apply,convolution_def]
  apply integral_eq_zero_of_ae
  filter_upwards [] with t
  change (𝓕 f : SchwartzMap ℝ ℂ) t*(𝓕 g : SchwartzMap ℝ ℂ) (eta-t)=0
  exact (h t).elim (fun hf => by rw [hf,zero_mul]) (fun hg => by rw [hg,mul_zero])

theorem lineSchwartzProduct_band (f g : SchwartzMap ℝ ℂ) (A B : ℝ)
    (hf : ∀ eta, (𝓕 f : SchwartzMap ℝ ℂ) eta≠0 → |eta|≤A)
    (hg : ∀ eta, (𝓕 g : SchwartzMap ℝ ℂ) eta≠0 → |eta|≤B) :
    ∀ eta, (𝓕 (lineSchwartzProduct f g) : SchwartzMap ℝ ℂ) eta≠0 → |eta|≤A+B := by
  intro eta heta
  by_contra hn
  apply heta
  apply lineSchwartzProduct_fourier_zero
  intro t
  by_cases ht : (𝓕 f : SchwartzMap ℝ ℂ) t=0
  · exact Or.inl ht
  · right
    by_contra hs
    have htri : |eta|≤|t|+|eta-t| := by simpa only [add_sub_cancel] using abs_add_le t (eta-t)
    exact hn (htri.trans (add_le_add (hf t ht) (hg (eta-t) hs)))

theorem lineSchwartzProduct_annular_lower (f g : SchwartzMap ℝ ℂ) (A B : ℝ)
    (hf : ∀ eta, (𝓕 f : SchwartzMap ℝ ℂ) eta≠0 → |eta|≤A)
    (hg : ∀ eta, (𝓕 g : SchwartzMap ℝ ℂ) eta≠0 → B≤|eta|) :
    ∀ eta, (𝓕 (lineSchwartzProduct f g) : SchwartzMap ℝ ℂ) eta≠0 → B-A≤|eta| := by
  intro eta heta
  by_contra hn
  apply heta
  apply lineSchwartzProduct_fourier_zero
  intro t
  by_cases ht : (𝓕 f : SchwartzMap ℝ ℂ) t=0
  · exact Or.inl ht
  · right
    by_contra hs
    have htri : |eta-t|≤|eta|+|t| := abs_sub eta t
    have h1 := hf t ht
    have h2 := hg (eta-t) hs
    linarith

end LipschitzHilbert.PacketRepresentation

end

end OAI
