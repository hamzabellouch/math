import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantChoiceMass
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantCompensationErrorFrequencies

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryGiantCompensationError
open Construction Conclusion Filter HistoryGiantFrequencyCount HistoryGiantCompensationProduct
open HistoryGiantChoiceMass HistorySignedResidues

theorem selected_choices_average_error_eventually
    (d : Decomposition) (Bs BD Bz : ℝ) {k : ℕ} (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L) ≤ C.blockBase →
      C.blockBase-2 < (C.giantCenter:ℝ) →
      (C.giantCenter:ℝ) < C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)| ≤ favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)| ≤ favorableBlockWidth L/16 →
      ∀ (m l : ℕ), l ≤ k → ∀ (a b : State),
      Template.Matches (Template.current (Template.initial m k) l) a.small →
      Template.Matches (Template.current (Template.initial m k) l) b.small →
      let seed := Template.initial m k
      let V := frequencyBound Bs BD Bz k L
      (∑ c : HistoryChoices C.sources seed V l, ∑ e : HistoryChoices C.sources seed V l,
        choicesMass C.sources seed V l c * choicesMass C.sources seed V l e *
          (((decodeHistory C.sources seed V l a c).compensationProduct : ℝ) *
            ((decodeHistory C.sources seed V l b e).compensationProduct : ℝ) *
              (30*Real.exp (-Real.exp (ScaleBudget.giant.target*L))))) ≤
        Real.exp (-Real.exp ((21/2000:ℝ)*L)) := by
  have hT := (actualFrequencyCost_pos Bs BD Bz hk).le
  filter_upwards [selected_cap_error_eventually Bs BD Bz
    (actualFrequencyCost Bs BD Bz k) k hT,
    selected_pair_compensationProduct_eventually d Bs BD Bz hk,
    (bulkSize_tendsto_atTop hk).eventually_ge_atTop 1,
    eventually_ge_atTop (0:ℝ)] with L herror hprod hm hL
  intro E C hG hcl hcu hb hd m l hl a b ha ha'
  dsimp only
  let seed := Template.initial m k
  let V := frequencyBound Bs BD Bz k L
  let r := 30*Real.exp (-Real.exp (ScaleBudget.giant.target*L))
  let B := (actualFactorCap Bs BD Bz k L)^(4*l*2^l)
  have hsum := paired_weighted_sum_le_of_ne_zero C.sources seed V l
    (fun c e => ((decodeHistory C.sources seed V l a c).compensationProduct : ℝ) *
      ((decodeHistory C.sources seed V l b e).compensationProduct : ℝ) * r) (B*r)
    (fun c e hc he => mul_le_mul_of_nonneg_right
      (hprod E C hG hcl hcu hb hd m l hl V a b c e ha ha' hc he) (by dsimp [r]; positivity))
  have hfreq : (Fintype.card (FrequencyChoices V l × FrequencyChoices V l) : ℝ) ≤
      Real.exp (rawLogBudget (actualFrequencyCost Bs BD Bz k) L) :=
    (actual_pair_card_le Bs BD Bz k L hL (by exact_mod_cast hm) hl).trans
      (Real.exp_le_exp.mpr (linear_le_rawLogBudget hT hL))
  calc
    _ ≤ (Fintype.card (FrequencyChoices V l × FrequencyChoices V l) : ℝ)*(B*r) := hsum
    _ = B*(Fintype.card (FrequencyChoices V l × FrequencyChoices V l) : ℝ)*r := by ring
    _ ≤ _ := herror l hl B _ (pow_nonneg (zero_le_one.trans (actualFactorCap_one_le Bs BD Bz k L)) _) le_rfl (Nat.cast_nonneg _) hfreq

end Ostmann.Arithmetic.HistoryGiantCompensationError

end

end OAI
