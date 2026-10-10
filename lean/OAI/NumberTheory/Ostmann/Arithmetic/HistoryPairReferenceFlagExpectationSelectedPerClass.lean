import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceFlagExpectationSelectedFamily

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairReferenceFlagExpectation
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistorySelectedFlagMassBounds HistoryUnnormalizedFlagError HistorySelectedPatternFlagError Filter
attribute [local instance] Classical.propDecidable
local instance selectedPerClassInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _

theorem selected_active_family_error_eventually (d : Decomposition) (Bs BD Bz C₀ : ℝ)
    {k : ℕ} (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop,∀(E : Finset ℕ)(C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L) ≤ C.blockBase →
      C.blockBase+favorableBlockWidth L ≤ Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2 < (C.giantCenter:ℝ) →
      (C.giantCenter:ℝ) < C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)| ≤ favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)| ≤ favorableBlockWidth L/16 →
      ∀l,l ≤ k → ∀outside : List ℕ,
      (∀p∈outside,0 < p) → outside.length ≤ bulkSize k L →
      (∀p∈outside,Real.log (p:ℝ) ≤ Real.exp ((1/1000:ℝ)*L)) →
      ∀f g : FrequencyChoices (frequencyBound Bs BD Bz k L) l,
      ∀p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l),
      ∀F : ActiveBlockFamily (fun _ : Bool=>C.giant) C.sources
        (Template.initial (2*(bulkSize k L/2)) k) (frequencyBound Bs BD Bz k L) outside l f g p,
      ∀A : ℝ,0 ≤ A → A ≤ selectedAmplitude C₀ k L l outside → F.WeightBound A →
      4*F.mean ≤ Real.exp (-Real.exp ((1/500:ℝ)*L)) := by
  filter_upwards [selected_reference_sourceMean_eventually d Bs BD Bz hk,
    selected_scaled_flag_error_sum_eventually Bs BD Bz (occurrenceCap k:ℝ) C₀
      (Nat.cast_nonneg _) hk] with L hsource hcost
  intro E C hG hGu hc hcu hb hd l hl outside hpos hlen hlog f g p F A hA hAA hw
  rcases F.zero_or_reference A hA hw with hz | ⟨y,_hy,hy,hmean⟩
  · rw [hz,mul_zero]
    exact Real.exp_nonneg _
  · let R := F.reference (F.outer y) hy
    have hu := hsource E C hG hGu hc hcu hb hd l hl outside p R
    have hmean' : F.mean ≤ A*selectedUnitBudget Bs BD Bz k L R.left.history R.right.history :=
      hmean.trans (mul_le_mul_of_nonneg_left hu hA)
    have hfour := mul_le_mul_of_nonneg_left hmean' (by norm_num : (0:ℝ) ≤ 4)
    have hstep := four_mul_unitBudget_le_selectedFlagCost Bs BD Bz C₀ k L
      outside R.left.history R.right.history hAA
    have hnumeric := hcost l hl R.left.history R.right.history R.left_labels R.right_labels
      outside hpos hlen hlog
    exact hfour.trans (hstep.trans hnumeric)

end Ostmann.Arithmetic.HistoryPairReferenceFlagExpectation

end

end OAI
