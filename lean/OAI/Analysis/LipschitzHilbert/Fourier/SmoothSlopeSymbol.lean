import OAI.Analysis.LipschitzHilbert.Fourier.NormalizedSymbolFamily
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

namespace OAI

/-! A smooth extension of the slope denominator gives the full normalized
symbol, including its slope partition and vertical frequency window. -/
noncomputable section
open scoped ContDiff
namespace LipschitzHilbert.PacketRepresentation

def positiveDenominator (c s : ℝ) : ℝ :=
  c/2+Real.smoothTransition ((s-c/2)/(c/2))*(s-c/2)

theorem positiveDenominator_lower (c : ℝ) (hc : 0<c) (s : ℝ) :
    c/2≤positiveDenominator c s := by
  unfold positiveDenominator
  by_cases hs : s≤c/2
  · rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr hs) (by positivity)), zero_mul, add_zero]
  · exact le_add_of_nonneg_right
      (mul_nonneg (Real.smoothTransition.nonneg _) (sub_nonneg.mpr (le_of_not_ge hs)))

theorem positiveDenominator_eq (c : ℝ) (hc : 0<c) (s : ℝ) (hs : c≤s) :
    positiveDenominator c s=s := by
  unfold positiveDenominator
  rw [Real.smoothTransition.one_of_one_le ((le_div_iff₀ (by positivity : (0:ℝ)<c/2)).2
    (by linarith only [hs])), one_mul]
  ring

theorem positiveDenominator_contDiff (c : ℝ) : ContDiff ℝ ∞ (positiveDenominator c) := by
  unfold positiveDenominator
  fun_prop

def masterVertical (z : MasterSymbolSpace) : ℝ := z.2.1+z.2.2*z.1 1

theorem masterVertical_contDiff : ContDiff ℝ ∞ masterVertical := by
  unfold masterVertical
  fun_prop

def masterSlopeArgument (c : ℝ) (z : MasterSymbolSpace) : ℝ :=
  -z.1 0/positiveDenominator c (masterVertical z)

theorem masterSlopeArgument_contDiff (c : ℝ) (hc : 0<c) :
    ContDiff ℝ ∞ (masterSlopeArgument c) := by
  apply ContDiff.div (by fun_prop) ((positiveDenominator_contDiff c).comp masterVertical_contDiff)
  intro z
  exact ne_of_gt ((by positivity : (0:ℝ)<c/2).trans_le (positiveDenominator_lower c hc (masterVertical z)))

theorem masterCutoff_hasCompactSupport (R : ℝ) (hR : 0<R) :
    HasCompactSupport (masterCutoff R hR : MasterSymbolSpace → ℂ) := by
  let b : ContDiffBump (0 : MasterSymbolSpace) := ⟨R,2*R,hR,by linarith⟩
  exact b.hasCompactSupport.comp_left (map_zero Complex.ofRealCLM)

def partitionedMasterSymbol (psi rho beta : SchwartzMap ℝ ℂ)
    (c : ℝ) (hc : 0<c) (R : ℝ) (hR : 0<R) : SchwartzMap MasterSymbolSpace ℂ :=
  let g := fun z : MasterSymbolSpace =>
    psi (masterArgument z)*rho (masterSlopeArgument c z)*beta (z.1 1)
  ((masterCutoff_hasCompactSupport R hR).mul_right (f' := g)).toSchwartzMap
    (((masterCutoff R hR).smooth ⊤).mul
      (((psi.smooth ⊤).comp masterArgument_temperate.1).mul
        ((rho.smooth ⊤).comp (masterSlopeArgument_contDiff c hc)) |>.mul (by fun_prop)))

theorem partitionedMasterSymbol_apply (psi rho beta : SchwartzMap ℝ ℂ)
    (c : ℝ) (hc : 0<c) (R : ℝ) (hR : 0<R) (z : MasterSymbolSpace) :
    partitionedMasterSymbol psi rho beta c hc R hR z=
      masterCutoff R hR z*(psi (masterArgument z)*rho (masterSlopeArgument c z)*beta (z.1 1)) := rfl

def partitionedSymbol (psi rho beta : SchwartzMap ℝ ℂ)
    (c : ℝ) (hc : 0<c) (R : ℝ) (hR : 0<R) (v t : ℝ) : SchwartzMap SymbolSpace ℂ :=
  symbolSlice (partitionedMasterSymbol psi rho beta c hc R hR) (v,t)

theorem partitionedSymbol_apply (psi rho beta : SchwartzMap ℝ ℂ)
    (c : ℝ) (hc : 0<c) (R : ℝ) (hR : 0<R) (v t X Y U : ℝ)
    (hxyz : ‖symbolPoint X Y U‖≤R) (hp : ‖(v,t)‖≤R) (hV : c≤v+t*Y) :
    partitionedSymbol psi rho beta c hc R hR v t (symbolPoint X Y U)=
      psi (X+(v+t*Y)*U)*rho (-X/(v+t*Y))*beta Y := by
  rw [partitionedSymbol, symbolSlice_apply, partitionedMasterSymbol_apply]
  have hz : ‖(symbolPoint X Y U,(v,t))‖≤R := by rw [Prod.norm_def]; exact max_le hxyz hp
  rw [masterCutoff_one R hR _ hz, one_mul]
  change psi (X+(v+t*Y)*U)*rho (-X/positiveDenominator c (v+t*Y))*beta Y=_
  rw [positiveDenominator_eq c hc _ hV]

theorem partitionedSymbol_uniform (psi rho beta : SchwartzMap ℝ ℂ)
    (c : ℝ) (hc : 0<c) (R : ℝ) (hR : 0<R) (q : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ v t : ℝ,
      symbolCoefficientBound (partitionedSymbol psi rho beta c hc R hR v t) q≤C := by
  obtain ⟨C,hC,h⟩ := symbolSlice_coefficient_uniform (partitionedMasterSymbol psi rho beta c hc R hR) q
  exact ⟨C,hC,fun v t => h (v,t)⟩

end LipschitzHilbert.PacketRepresentation

end

end OAI
