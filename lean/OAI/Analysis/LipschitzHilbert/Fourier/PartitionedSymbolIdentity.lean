import OAI.Analysis.LipschitzHilbert.Fourier.SmoothSlopeSymbol
import OAI.Analysis.LipschitzHilbert.Fourier.LocalizedSymbolIdentity

namespace OAI

/-! Exact separation of the full symbol, including the frequency-slope
partition and the vertical bin window, with annular selector support. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem partitionedSymbol_factor (psi rho beta : SchwartzMap ℝ ℂ)
    (c : ℝ) (hc : 0<c) (R : ℝ) (hR : 0<R) (v t X Y U : ℝ) :
    partitionedSymbol psi rho beta c hc R hR v t (symbolPoint X Y U)=
      normalizedSchwartzSymbol psi R hR v t (symbolPoint X Y U)*
        rho (-X/positiveDenominator c (v+t*Y))*beta Y := by
  rw [partitionedSymbol, symbolSlice_apply, partitionedMasterSymbol_apply,
    normalizedSchwartzSymbol_apply]
  change masterCutoff R hR (symbolPoint X Y U,(v,t))*
      (psi (X+(v+t*Y)*U)*rho (-X/positiveDenominator c (v+t*Y))*beta Y)=
    psi (X+(v+t*Y)*U)*masterCutoff R hR (symbolPoint X Y U,(v,t))*
      rho (-X/positiveDenominator c (v+t*Y))*beta Y
  ring

theorem partitionedSymbol_eq (psi rho beta : SchwartzMap ℝ ℂ)
    (A B c M R : ℝ) (hR : 0<R) (hc : 0<c)
    (hpsi : ∀ s : ℝ, M < |s| → psi s=0) (hsize : A+B+(M+A)/c≤R)
    (v t X Y U : ℝ) (hp : ‖(v,t)‖≤R) (hX : |X|≤A) (hY : |Y|≤B) (hV : c≤v+t*Y) :
    partitionedSymbol psi rho beta c hc R hR v t (symbolPoint X Y U)=
      psi (X+(v+t*Y)*U)*rho (-X/(v+t*Y))*beta Y := by
  rw [partitionedSymbol_factor,
    normalizedSchwartzSymbol_eq psi A B c M R hR hc hpsi hsize v t X Y U hp hX hY hV,
    positiveDenominator_eq c hc _ hV]

theorem partitioned_annular_multiplier (psi rho beta : SchwartzMap ℝ ℂ)
    (A B c C a M R : ℝ) (hR : 0<R) (hc : 0<c) (hC : 0<C) (ha : 0<a)
    (hM : 0<M) (hA : 0≤A) (hsmall : A≤a/4)
    (hpsi : ∀ s : ℝ, psi s≠0 → a≤|s| ∧ |s|≤M) (hsize : A+B+(M+A)/c≤R)
    (v t X Y U : ℝ) (hp : ‖(v,t)‖≤R) (hX : |X|≤A) (hY : |Y|≤B)
    (hV : c≤v+t*Y) (hVC : v+t*Y≤C) (q : ℕ) :
    psi (X+(v+t*Y)*U)*rho (-X/(v+t*Y))*beta Y=
      ∫ nu : SymbolSpace,
        (symbolWeight q nu:ℂ)*((symbolWeight q nu:ℂ)*frequencyCharacter nu X Y)*
          (symbolWeight q nu:ℂ)*localizedSelector
            (annularCutoff (3*a/(4*C)) ((M+A)/c) (by positivity) (by positivity))
            (partitionedSymbol psi rho beta c hc R hR v t) q nu U := by
  rw [← localized_symbol_identity, partitionedSymbol_factor,
    positiveDenominator_eq c hc _ hV]
  have hbase := localized_annular_multiplier psi A B c C a M R hR hc hC ha hM hA hsmall
    hpsi hsize v t X Y U hp hX hY hV hVC q
  rw [← localized_symbol_identity] at hbase
  calc
    _ = ((annularCutoff (3*a/(4*C)) ((M+A)/c) (by positivity) (by positivity) U:ℝ):ℂ)*
        normalizedSchwartzSymbol psi R hR v t (symbolPoint X Y U)*
          rho (-X/(v+t*Y))*beta Y := by rw [← hbase]
    _ = _ := by ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
