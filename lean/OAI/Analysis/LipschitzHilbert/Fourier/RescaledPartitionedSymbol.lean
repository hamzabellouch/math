import OAI.Analysis.LipschitzHilbert.Fourier.RescaledAnnularSymbol
import OAI.Analysis.LipschitzHilbert.Fourier.PartitionedSymbolIdentity

namespace OAI

/-! The slope partition is rescaled together with the angular variable,
so its argument remains the original frequency slope divided by w/l. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

def realDilation (H : ℝ) (hH : H≠0) : ℝ ≃L[ℝ] ℝ :=
  { LinearEquiv.smulOfNeZero ℝ ℝ H hH with
    continuous_toFun := by change Continuous (fun x : ℝ => H*x); fun_prop
    continuous_invFun := by change Continuous (fun x : ℝ => H⁻¹*x); fun_prop }

def dilatedSlopeWindow (rho : SchwartzMap ℝ ℂ) (H : ℝ) (hH : H≠0) : SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (realDilation H hH) rho

theorem dilatedSlopeWindow_apply (rho : SchwartzMap ℝ ℂ) (H : ℝ) (hH : H≠0) (x : ℝ) :
    dilatedSlopeWindow rho H hH x=rho (H*x) := rfl

theorem rescaled_partitioned_symbol_eq (psi rho beta : SchwartzMap ℝ ℂ)
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
      partitionedSymbol psi (dilatedSlopeWindow rho H hH.ne') beta (H*c) (mul_pos hH hc) R hR
        (H*w*center) (H*w/W)
        (symbolPoint (symbolX l xi eta theta) (symbolY W eta center) (symbolU l (H*w) u theta))=
      psi (l*(xi+u*eta))*rho (-symbolX l xi eta theta/(w*eta))*beta (symbolY W eta center) := by
  have hvertical : H*w*center+(H*w/W)*symbolY W eta center=H*(w*eta) := by
    unfold symbolY
    field_simp
    ring
  have hVlo : H*c≤H*w*center+(H*w/W)*symbolY W eta center := by
    rw [hvertical]
    exact mul_le_mul_of_nonneg_left hlo hH.le
  have hwe : 0<w*eta := hc.trans_le hlo
  rw [partitionedSymbol_factor,positiveDenominator_eq (H*c) (mul_pos hH hc) _ hVlo,
    dilatedSlopeWindow_apply,hvertical]
  have hrho : H*(-symbolX l xi eta theta/(H*(w*eta)))=
      -symbolX l xi eta theta/(w*eta) := by field_simp
  rw [hrho]
  rw [←mul_assoc,←mul_assoc,
    rescaled_localized_symbol_eq psi A B c C a M R H hR hH hc hC ha hM hA hsmall
      hpsi hsize l w W theta center u xi eta hl hw hW hparam hX hY hlo hhi]

end LipschitzHilbert.PacketRepresentation

end

end OAI
