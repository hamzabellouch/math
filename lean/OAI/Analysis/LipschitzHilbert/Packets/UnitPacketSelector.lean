import OAI.Analysis.LipschitzHilbert.Estimates.LocalizedSelectorDerivative
import Mathlib.Analysis.Calculus.MeanValue

namespace OAI

/-! The compact Fourier selectors are normalized to the size and
Lipschitz bounds required by the finite packet model. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

def selectorNormalizer (chi : SchwartzMap ℝ ℝ) (C : ℝ) : ℝ :=
  C*(1+SchwartzMap.seminorm ℝ 0 1 chi+2*Real.pi)

theorem selectorNormalizer_pos (chi : SchwartzMap ℝ ℝ) (C : ℝ) (hC : 0<C) :
    0<selectorNormalizer chi C := by unfold selectorNormalizer; positivity

def unitPacketSelector (chi : SchwartzMap ℝ ℝ) (C : ℝ) (S : SchwartzMap SymbolSpace ℂ)
    (q : ℕ) (nu : SymbolSpace) (U : ℝ) : ℂ :=
  ((selectorNormalizer chi C)⁻¹:ℂ)*localizedSelector chi S q nu U

theorem unitPacketSelector_differentiable (chi : SchwartzMap ℝ ℝ) (C : ℝ)
    (S : SchwartzMap SymbolSpace ℂ) (q : ℕ) (nu : SymbolSpace) :
    Differentiable ℝ (unitPacketSelector chi C S q nu) := by
  intro U
  exact (((chi.hasDerivAt U).ofReal_comp.mul (weightedSelector_hasDerivAt S q nu U)).const_mul
    ((selectorNormalizer chi C)⁻¹:ℂ)).differentiableAt

theorem unitPacketSelector_bound (chi : SchwartzMap ℝ ℝ) (hchi : ∀ U, |chi U|≤1)
    (C : ℝ) (hC : 0<C) (S : SchwartzMap SymbolSpace ℂ) (q : ℕ)
    (hS : symbolCoefficientBound S q≤C) (nu : SymbolSpace) (U : ℝ) :
    ‖unitPacketSelector chi C S q nu U‖≤1 := by
  have hM := selectorNormalizer_pos chi C hC
  have hCM : C≤selectorNormalizer chi C := by
    unfold selectorNormalizer
    nlinarith only [hC, apply_nonneg (SchwartzMap.seminorm ℝ 0 1) chi, Real.pi_pos]
  have hb : ‖localizedSelector chi S q nu U‖≤C :=
    (localizedSelector_bound chi hchi S q nu U).trans
      (((mul_le_mul_of_nonneg_right hS (symbolWeight_pos q nu).le).trans
        (by simpa only [mul_one] using mul_le_mul_of_nonneg_left (symbolWeight_le_one q nu) hC.le)))
  rw [unitPacketSelector, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM]
  exact (mul_le_mul_of_nonneg_left (hb.trans hCM) (inv_nonneg.mpr hM.le)).trans_eq
    (inv_mul_cancel₀ hM.ne')

theorem unitPacketSelector_deriv_bound (chi : SchwartzMap ℝ ℝ) (hchi : ∀ U, |chi U|≤1)
    (C : ℝ) (hC : 0<C) (S : SchwartzMap SymbolSpace ℂ) (q : ℕ) (hq : 1≤q)
    (hS : symbolCoefficientBound S q≤C) (nu : SymbolSpace) (U : ℝ) :
    ‖deriv (unitPacketSelector chi C S q nu) U‖≤1 := by
  have hM := selectorNormalizer_pos chi C hC
  have hd : HasDerivAt (localizedSelector chi S q nu) _ U :=
    (chi.hasDerivAt U).ofReal_comp.mul (weightedSelector_hasDerivAt S q nu U)
  have hc := hd.const_mul ((selectorNormalizer chi C)⁻¹:ℂ)
  change HasDerivAt (unitPacketSelector chi C S q nu) _ U at hc
  rw [hc.deriv, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM, ← hd.deriv]
  have hb : ‖deriv (localizedSelector chi S q nu) U‖≤selectorNormalizer chi C := by
    apply (localizedSelector_deriv_bound chi hchi S q hq nu U).trans
    have hnonneg : 0≤SchwartzMap.seminorm ℝ 0 1 chi+2*Real.pi := by positivity
    have h := mul_le_mul_of_nonneg_left hS hnonneg
    unfold selectorNormalizer
    nlinarith only [h,hC]
  exact (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hM.le)).trans_eq (inv_mul_cancel₀ hM.ne')

theorem unitPacketSelector_lipschitz (chi : SchwartzMap ℝ ℝ) (hchi : ∀ U, |chi U|≤1)
    (C : ℝ) (hC : 0<C) (S : SchwartzMap SymbolSpace ℂ) (q : ℕ) (hq : 1≤q)
    (hS : symbolCoefficientBound S q≤C) (nu : SymbolSpace) :
    LipschitzWith 1 (unitPacketSelector chi C S q nu) := by
  apply lipschitzWith_of_nnnorm_deriv_le (unitPacketSelector_differentiable chi C S q nu)
  intro U
  exact_mod_cast unitPacketSelector_deriv_bound chi hchi C hC S q hq hS nu U

end LipschitzHilbert.PacketRepresentation

end

end OAI
