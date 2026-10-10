import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantCompensationErrorSelected
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantFrequencyCount

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantCompensationError
open Construction Conclusion Filter HistoryGiantFrequencyCount

theorem selected_frequency_compensation_error_eventually
    (d : Decomposition) (Bs BD Bz : ℝ) {k : ℕ} (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L) ≤ C.blockBase →
      C.blockBase-2 < (C.giantCenter:ℝ) →
      (C.giantCenter:ℝ) < C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)| ≤ favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)| ≤ favorableBlockWidth L/16 →
      ∀ (m l : ℕ), l ≤ k → ∀ (a b : State)
        (c e : HistoryChoices C.sources (Template.initial m k)
          (frequencyBound Bs BD Bz k L) l),
      Template.Matches (Template.current (Template.initial m k) l) a.small →
      Template.Matches (Template.current (Template.initial m k) l) b.small →
      choicesMass C.sources (Template.initial m k) (frequencyBound Bs BD Bz k L) l c ≠ 0 →
      choicesMass C.sources (Template.initial m k) (frequencyBound Bs BD Bz k L) l e ≠ 0 →
      (((decodeHistory C.sources (Template.initial m k) (frequencyBound Bs BD Bz k L)
          l a c).compensationProduct : ℝ) *
        ((decodeHistory C.sources (Template.initial m k) (frequencyBound Bs BD Bz k L)
          l b e).compensationProduct : ℝ))*
        (Fintype.card (FrequencyChoices (frequencyBound Bs BD Bz k L) l ×
          FrequencyChoices (frequencyBound Bs BD Bz k L) l) : ℝ)*
          (30*Real.exp (-Real.exp (ScaleBudget.giant.target*L))) ≤
            Real.exp (-Real.exp ((21/2000:ℝ)*L)) := by
  have hT := (actualFrequencyCost_pos Bs BD Bz hk).le
  filter_upwards [selected_compensation_error_eventually d Bs BD Bz
    (actualFrequencyCost Bs BD Bz k) hT hk,
    (bulkSize_tendsto_atTop hk).eventually_ge_atTop 1,
    eventually_ge_atTop (0:ℝ)] with L he hm hL
  intro E C hG hcl hcu hb hd m l hl a b c e ha ha' hc hc'
  apply he E C hG hcl hcu hb hd m l hl (frequencyBound Bs BD Bz k L)
    a b c e ha ha' hc hc' _ (Nat.cast_nonneg _)
  exact (actual_pair_card_le Bs BD Bz k L hL (by exact_mod_cast hm) hl).trans
    (Real.exp_le_exp.mpr (linear_le_rawLogBudget hT hL))

end Ostmann.Arithmetic.HistoryGiantCompensationError

end

end OAI
