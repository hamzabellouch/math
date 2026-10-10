import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairVariableBSquareErrorSelectedBudget
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairVariableBSquareErrorSelectedWeighted

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryPairVariableBSquareErrorSelected
open Construction CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairSourceLaws HistoryCompensationBiasedKernelSum HistoryPairKernelReplacement
open HistoryPairVariableBSquareErrorSelectedKernel HistoryPairVariableBSquareErrorSelectedSum
open HistoryPairRepresentatives Conclusion Filter
local instance (seed : List SourceSlot) (l : ℕ) : DecidableEq (Internal seed l) := Classical.decEq _

theorem selected_originalDecodedBErrorSum_scaled_eventually
    (d : Decomposition) (Bs BD Bz A D : ℝ) {k : ℕ} (hk : 2 ≤ k) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L) ≤ C.blockBase →
      C.blockBase+favorableBlockWidth L ≤ Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2 < (C.giantCenter:ℝ) →
      (C.giantCenter:ℝ) < C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)| ≤ favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)| ≤ favorableBlockWidth L/16 →
      ∀ l : ℕ, l ≤ k →
      let seed := Template.initial (2*(bulkSize k L/2)) k
      ∀ (mixed : Bool) (V : ℕ → ℕ) (outside : List ℕ),
      (∀ p ∈ outside, 0 < p) → outside.length ≤ bulkSize k L →
      (∀ p ∈ outside, Real.log (p:ℝ) ≤ Real.exp ((1/1000:ℝ)*L)) →
      ∀ {spectator : PrimeSource}, C.CrossRoleSeparation spectator →
      (∀ j ≤ l, ∀ origin, (C.sources origin).AboveFrequency (V j)) →
      ∀ (refs : ∀p:Pattern (pairedHistoryType seed l),
        (b:Block p → CommonSample C.sources (pairedInternalOrigin seed l)) →
          Option (DecodedSquareReference C (pairedInternalOrigin seed l)
            (pairedHistoryType seed l) p b V outside l))
        (mask : ∀p:Pattern (pairedHistoryType seed l),
          (Block p → CommonSample C.sources (pairedInternalOrigin seed l)) → ℝ),
      (∀p b, 0 ≤ mask p b ∧ mask p b ≤ 1) →
      (((outside.prod:ℝ)^(2^(l+1))*Real.exp (A*((bulkSize k L:ℝ)+1))) *
        Real.exp (D*(L+1)^2)) *
        ‖originalDecodedBErrorSum C (pairedInternalOrigin seed l) (pairedHistoryType seed l)
          mixed V outside l refs mask‖ ≤ Real.exp (-Real.exp ((1/500:ℝ)*L)) := by
  filter_upwards [selected_originalDecodedBErrorSum_eventually d Bs BD Bz hk,
    selected_square_loss_budget_eventually k A D] with L herr hbudget
  intro E C hG hGu hcl hcu hb hd l hl
  dsimp only
  intro mixed V outside hpos hlen hlog spectator hsep hV refs mask hm
  have he := herr E C hG hGu hcl hcu hb hd l hl mixed V outside hsep hV refs mask hm
  have hs := hbudget l hl outside hpos hlen hlog
  have h := mul_le_mul_of_nonneg_left he (by positivity :
    0 ≤ ((outside.prod:ℝ)^(2^(l+1))*Real.exp (A*((bulkSize k L:ℝ)+1)))*
      Real.exp (D*(L+1)^2))
  exact h.trans (by simpa only [mul_assoc] using hs)

theorem selected_weightedOriginalDecodedBErrorSum_scaled_eventually
    (d : Decomposition) (Bs BD Bz A D : ℝ) {k : ℕ} (hk : 2 ≤ k) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L) ≤ C.blockBase →
      C.blockBase+favorableBlockWidth L ≤ Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2 < (C.giantCenter:ℝ) →
      (C.giantCenter:ℝ) < C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)| ≤ favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)| ≤ favorableBlockWidth L/16 →
      ∀ l : ℕ, l ≤ k →
      let seed := Template.initial (2*(bulkSize k L/2)) k
      ∀ (mixed : Bool) (V : ℕ → ℕ) (outside : List ℕ),
      (∀ p ∈ outside, 0 < p) → outside.length ≤ bulkSize k L →
      (∀ p ∈ outside, Real.log (p:ℝ) ≤ Real.exp ((1/1000:ℝ)*L)) →
      ∀ {spectator : PrimeSource}, C.CrossRoleSeparation spectator →
      (∀ j ≤ l, ∀ origin, (C.sources origin).AboveFrequency (V j)) →
      ∀ (refs : ∀p:Pattern (pairedHistoryType seed l),
        (b:Block p → CommonSample C.sources (pairedInternalOrigin seed l)) →
          Option (DecodedSquareReference C (pairedInternalOrigin seed l)
            (pairedHistoryType seed l) p b V outside l))
        (mask : ∀p:Pattern (pairedHistoryType seed l),
          (Block p → CommonSample C.sources (pairedInternalOrigin seed l)) → ℝ),
      (∀p b, 0 ≤ mask p b ∧ mask p b ≤ 1) →
      ∀ (amp : ∀p:Pattern (pairedHistoryType seed l),
        BlockDraw p (CommonSample C.sources (pairedInternalOrigin seed l)) → ℂ),
      (∀p b, ‖amp p b‖ ≤
        ((outside.prod:ℝ)^(2^(l+1))*Real.exp (A*((bulkSize k L:ℝ)+1)))*
          Real.exp (D*(L+1)^2)) →
      ‖weightedOriginalDecodedBErrorSum C (pairedInternalOrigin seed l) (pairedHistoryType seed l)
        mixed V outside l refs mask amp‖ ≤ Real.exp (-Real.exp ((1/500:ℝ)*L)) := by
  filter_upwards [selected_weightedOriginalDecodedBErrorSum_eventually d Bs BD Bz hk,
    selected_square_loss_budget_eventually k A D] with L herr hbudget
  intro E C hG hGu hcl hcu hb hd l hl
  dsimp only
  intro mixed V outside hpos hlen hlog spectator hsep hV refs mask hm amp hamp
  have he := herr E C hG hGu hcl hcu hb hd l hl mixed V outside hsep hV refs mask hm
    (((outside.prod:ℝ)^(2^(l+1))*Real.exp (A*((bulkSize k L:ℝ)+1)))*
      Real.exp (D*(L+1)^2)) (by positivity) amp hamp
  have hs := hbudget l hl outside hpos hlen hlog
  exact he.trans (by convert hs using 1)

end Ostmann.Arithmetic.HistoryPairVariableBSquareErrorSelected

end

end OAI
