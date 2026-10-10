import OAI.Analysis.LipschitzHilbert.Fourier.LocalizedSymbolIdentity

namespace OAI

/-! The fixed angular enlargement is an exact change of normalized
coordinates. The annular cutoff and the compact master symbol are still
one on every contributing frequency. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

theorem rescaled_symbol_coordinates (H l w W theta center u xi eta : ℝ)
    (hH : H≠0) (hl : l≠0) (hw : w≠0) (hW : W≠0) :
    symbolX l xi eta theta+
      (H*w*center+(H*w/W)*symbolY W eta center)*symbolU l (H*w) u theta=
      l*(xi+u*eta) := by
  unfold symbolX symbolY symbolU
  field_simp
  ring

theorem rescaled_localized_symbol_eq (psi : SchwartzMap ℝ ℂ)
    (A B c C a M R H : ℝ) (hR : 0<R) (hH : 0<H)
    (hc : 0<c) (hC : 0<C) (ha : 0<a) (hM : 0<M)
    (hA : 0≤A) (hsmall : A≤a/4)
    (hpsi : ∀ s : ℝ, psi s≠0 → a≤|s| ∧ |s|≤M)
    (hsize : A+B+(M+A)/(H*c)≤R)
    (l w W theta center u xi eta : ℝ) (hl : 0<l) (hw : 0<w) (hW : 0<W)
    (hparam : ‖(H*w*center,H*w/W)‖≤R)
    (hX : |symbolX l xi eta theta|≤A) (hY : |symbolY W eta center|≤B)
    (hlo : c≤w*eta) (hhi : w*eta≤C) :
    (annularCutoff (3*a/(4*(H*C))) ((M+A)/(H*c)) (by positivity) (by positivity)
      (symbolU l (H*w) u theta):ℂ)*
      normalizedSchwartzSymbol psi R hR (H*w*center) (H*w/W)
        (symbolPoint (symbolX l xi eta theta) (symbolY W eta center) (symbolU l (H*w) u theta))=
      psi (l*(xi+u*eta)) := by
  have hvertical : H*w*center+(H*w/W)*symbolY W eta center=H*(w*eta) := by
    unfold symbolY
    field_simp
    ring
  have hVlo : H*c≤H*w*center+(H*w/W)*symbolY W eta center := by
    rw [hvertical]
    exact mul_le_mul_of_nonneg_left hlo hH.le
  have hVhi : H*w*center+(H*w/W)*symbolY W eta center≤H*C := by
    rw [hvertical]
    exact mul_le_mul_of_nonneg_left hhi hH.le
  have heq := localized_annular_multiplier psi A B (H*c) (H*C) a M R hR
    (mul_pos hH hc) (mul_pos hH hC) ha hM hA hsmall hpsi hsize
    (H*w*center) (H*w/W) (symbolX l xi eta theta) (symbolY W eta center)
    (symbolU l (H*w) u theta) hparam hX hY hVlo hVhi 0
  rw [←localized_symbol_identity] at heq
  rw [rescaled_symbol_coordinates H l w W theta center u xi eta hH.ne' hl.ne' hw.ne' hW.ne'] at heq
  exact heq.symm


/-- A vertical frequency window inherits the original annulus from its
center and width, with the exact endpoint allowance. -/
theorem vertical_annulus_from_window (w W center eta B c C : ℝ)
    (hw : 0<w) (hW : 0<W)
    (hlo : c+B*(w/W)≤w*center) (hhi : w*center+B*(w/W)≤C)
    (hY : |symbolY W eta center|≤B) : c≤w*eta ∧ w*eta≤C := by
  have hy := abs_le.mp hY
  have hp : 0≤w/W := (div_pos hw hW).le
  have hcancel : (w/W)*symbolY W eta center=w*(eta-center) := by
    unfold symbolY
    field_simp
  have hleft := mul_le_mul_of_nonneg_left hy.1 hp
  have hright := mul_le_mul_of_nonneg_left hy.2 hp
  rw [hcancel] at hleft hright
  constructor <;> nlinarith

end LipschitzHilbert.PacketRepresentation

end

end OAI
