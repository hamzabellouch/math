import OAI.Analysis.LipschitzHilbert.Fourier.AnnularSelector

namespace OAI

/-! The exact separated symbol with compact annular selectors. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem localized_symbol_identity (chi : SchwartzMap ℝ ℝ) (S : SchwartzMap SymbolSpace ℂ)
    (q : ℕ) (X Y U : ℝ) :
    (chi U : ℂ)*S (symbolPoint X Y U)=∫ nu : SymbolSpace,
      (symbolWeight q nu : ℂ)*((symbolWeight q nu : ℂ)*frequencyCharacter nu X Y)*
        (symbolWeight q nu : ℂ)*localizedSelector chi S q nu U := by
  rw [weighted_symbol_identity S q X Y U, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with nu
  unfold localizedSelector
  ring

theorem localized_annular_multiplier (psi : SchwartzMap ℝ ℂ)
    (A B c C a M R : ℝ) (hR : 0<R) (hc : 0<c) (hC : 0<C) (ha : 0<a)
    (hM : 0<M) (hA : 0≤A) (hsmall : A≤a/4)
    (hpsi : ∀ s : ℝ, psi s≠0 → a≤|s| ∧ |s|≤M)
    (hsize : A+B+(M+A)/c≤R)
    (v t X Y U : ℝ) (hp : ‖(v,t)‖≤R)
    (hX : |X|≤A) (hY : |Y|≤B) (hV : c≤v+t*Y) (hVC : v+t*Y≤C) (q : ℕ) :
    psi (X+(v+t*Y)*U)=∫ nu : SymbolSpace,
      (symbolWeight q nu : ℂ)*((symbolWeight q nu : ℂ)*frequencyCharacter nu X Y)*
        (symbolWeight q nu : ℂ)*localizedSelector
          (annularCutoff (3*a/(4*C)) ((M+A)/c) (by positivity) (by positivity))
          (normalizedSchwartzSymbol psi R hR v t) q nu U := by
  rw [← localized_symbol_identity]
  have htail : ∀ s : ℝ, M < |s| → psi s=0 := by
    intro s hs
    by_contra hn
    exact (not_lt_of_ge (hpsi s hn).2) hs
  rw [normalizedSchwartzSymbol_eq psi A B c M R hR hc htail hsize v t X Y U hp hX hY hV]
  by_cases hz : psi (X+(v+t*Y)*U)=0
  · rw [hz, mul_zero]
  · have hlo := normalized_selector_lower X (v+t*Y) U a C ha hC
      (hc.le.trans hV) hVC (hX.trans hsmall) (hpsi _ hz).1
    have hhi : |U|≤(M+A)/c := by
      have h := normalized_selector_upper X (v+t*Y) U c (4*A) M hc hV
        (by nlinarith only [hX]) (hpsi _ hz).2
      simpa only [mul_div_cancel_left₀ A (by norm_num : (4:ℝ)≠0)] using h
    rw [annularCutoff_one _ _ _ _ U hlo hhi, Complex.ofReal_one, one_mul]

end LipschitzHilbert.PacketRepresentation

end

end OAI
