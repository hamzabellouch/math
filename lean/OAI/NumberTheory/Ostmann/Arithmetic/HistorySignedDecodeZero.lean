import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedDecodeRebuild
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedDecodeSupportedIntegral

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedDecode
open Construction

theorem SignedHistory.PositiveIntegral.pivotsPositive {l : ℕ} {h : SignedHistory l}
    (hi : h.PositiveIntegral) : h.PivotsPositive := by
  induction h with
  | leaf a => trivial
  | node a p u hp hm left right il ir =>
    exact ⟨hi.2.1,il hi.2.2.2.2.1,ir hi.2.2.2.2.2⟩

theorem decoded_weight_eq_zero_of_not_positiveIntegral
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ)
    (l : ℕ) (a : State) (c : HistoryChoices sources seed V l) (outside : List ℕ)
    (base : State → ℂ) (φ : ℝ → ℝ) (G : ℝ)
    (hi : ¬(signedDecode sources seed V l (SignedState.ofState a) c).PositiveIntegral) :
    (decodeHistory sources seed V l a c).supportedWeight V outside base φ G=0 := by
  apply History.supportedWeight_of_not_supported
  intro hs
  exact hi (signedDecode_ofState_positiveIntegral_of_supported sources seed V l a c outside hs)

theorem decoded_weight_eq_zero_of_not_pivotsPositive
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ)
    (l : ℕ) (a : State) (c : HistoryChoices sources seed V l) (outside : List ℕ)
    (base : State → ℂ) (φ : ℝ → ℝ) (G : ℝ)
    (hi : ¬(signedDecode sources seed V l (SignedState.ofState a) c).PivotsPositive) :
    (decodeHistory sources seed V l a c).supportedWeight V outside base φ G=0 :=
  decoded_weight_eq_zero_of_not_positiveIntegral sources seed V l a c outside base φ G
    (fun hp => hi hp.pivotsPositive)

theorem decoded_weight_eq_zero_of_not_integralGuard
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ)
    (l : ℕ) (a : State) (c : HistoryChoices sources seed V l) (outside : List ℕ)
    (base : State → ℂ) (φ : ℝ → ℝ) (G : ℝ)
    (hi : ¬(signedDecode sources seed V l (SignedState.ofState a) c).IntegralGuard) :
    (decodeHistory sources seed V l a c).supportedWeight V outside base φ G=0 :=
  decoded_weight_eq_zero_of_not_positiveIntegral sources seed V l a c outside base φ G
    (fun hp => hi hp.integralGuard)

theorem rebuild_decodeHistory_toHistory_of_positiveIntegral
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ)
    (l : ℕ) (a : State) (c : HistoryChoices sources seed V l) (Xp Xm : ℤ)
    (hi : (rebuild (decodeHistory sources seed V l a c) Xp Xm).PositiveIntegral) :
    (rebuild (decodeHistory sources seed V l a c) Xp Xm).toHistory=
      decodeHistory sources seed V l ⟨a.frequency,Xp.toNat,Xm.toNat,a.small⟩ c := by
  rw [rebuild_decodeHistory] at hi ⊢
  exact signedDecode_toHistory_of_positiveIntegral sources seed V l _ c hi

end Ostmann.Arithmetic.HistorySignedDecode

end

end OAI
