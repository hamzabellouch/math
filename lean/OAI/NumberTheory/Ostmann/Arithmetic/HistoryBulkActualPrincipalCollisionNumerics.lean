import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceFrequencyFamilyRoots
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantFrequencyCount
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedRootFlagErrorRates

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalCollision
open Construction Conclusion Filter HistoryGiantFrequencyCount HistorySelectedRootFlagError HistoryBulkReferenceFrequencyFamily

theorem selected_index_collision_error_eventually (Bs BD Bz H : ℝ)
    (hH : 0≤H) {k : ℕ} (hk : 0<k) :
    ∀ᶠ L : ℝ in atTop,∀l≤k,
      (Fintype.card (RootFrequencyIndex (frequencyBound Bs BD Bz k L) l):ℝ)*
        Real.exp (-Real.exp ((1/500:ℝ)*L)) ≤
          Real.exp (-frequencyBudget Bs BD Bz k L l-H*(bulkSize k L:ℝ)) ∧
      (Fintype.card (RootFrequencyIndex (frequencyBound Bs BD Bz k L) l):ℝ)*
        Real.exp (-Real.exp ((1/500:ℝ)*L)) ≤ Real.exp (-H*(bulkSize k L:ℝ)) := by
  let D := actualFrequencyCost Bs BD Bz k
  filter_upwards [selected_root_collision_error_eventually Bs BD Bz 1 D H (by norm_num) hH hk,
    (bulkSize_tendsto_atTop hk).eventually_ge_atTop 1,eventually_ge_atTop (0:ℝ)] with L he hm hL
  intro l hl
  have hc := actual_pair_card_le Bs BD Bz k L hL (by exact_mod_cast hm) hl
  have hD : 0≤D := (actualFrequencyCost_pos Bs BD Bz hk).le
  have hLsq : L≤(L+1)^2 := by nlinarith [sq_nonneg L]
  have hce : (Fintype.card (FrequencyChoices (frequencyBound Bs BD Bz k L) l ×
      FrequencyChoices (frequencyBound Bs BD Bz k L) l):ℝ)≤Real.exp (D*(L+1)^2) :=
    hc.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hLsq hD))
  have hs : (Fintype.card (RootFrequencyIndex (frequencyBound Bs BD Bz k L) l):ℝ)*
      Real.exp (-Real.exp ((1/500:ℝ)*L))≤
      (Fintype.card (AllowedFrequency (frequencyBound Bs BD Bz k L) l):ℝ)*1*
        Real.exp (D*(L+1)^2)*Real.exp (-Real.exp ((1/500:ℝ)*L)) := by
    simp only [RootFrequencyIndex,Fintype.card_prod,Nat.cast_mul] at hce ⊢
    simpa only [mul_one,mul_assoc] using
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hce (Nat.cast_nonneg (Fintype.card
          (AllowedFrequency (frequencyBound Bs BD Bz k L) l)))) (Real.exp_nonneg _)
  exact ⟨hs.trans (he l hl).1,hs.trans (he l hl).2⟩

end Ostmann.Arithmetic.HistoryBulkActualPrincipalCollision

end

end OAI
