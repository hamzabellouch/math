import OAI.NumberTheory.Ostmann.Arithmetic.HistoryActualComparisonDecayArithmetic
import OAI.NumberTheory.Ostmann.Conclusion.Scales

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryActualComparisonDecayArithmetic
open Conclusion Filter

theorem eventually_five_stage_exp_le {k : ℕ} (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop, ∀ F H : ℝ, ∀ z : Fin 6 → ℂ,
      (∀ i : Fin 5, ‖z i.castSucc-z i.succ‖ ≤
        Real.exp (-F-(H+5)*(bulkSize k L:ℝ))) →
      ‖z 0-z 5‖ ≤ Real.exp (-F-H*(bulkSize k L:ℝ)) := by
  filter_upwards [(bulkSize_tendsto_atTop hk).eventually_ge_atTop 1] with L hm
  intro F H z hz
  exact five_stage_exp_le_of_steps hm z hz

theorem eventually_five_stage_bulk_exp_le {k : ℕ} (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop, ∀ H : ℝ, ∀ z : Fin 6 → ℂ,
      (∀ i : Fin 5, ‖z i.castSucc-z i.succ‖ ≤
        Real.exp (-(H+5)*(bulkSize k L:ℝ))) →
      ‖z 0-z 5‖ ≤ Real.exp (-H*(bulkSize k L:ℝ)) := by
  filter_upwards [eventually_five_stage_exp_le hk] with L h
  intro H z hz
  simpa only [neg_zero,zero_sub,neg_mul] using
    h 0 H z (fun i => by simpa only [neg_zero,zero_sub,neg_mul] using hz i)

theorem eventually_two_terms_exp_67_65_le {k : ℕ} (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop, ∀ F a b : ℝ,
      a ≤ Real.exp (-(F+67*(2:ℝ)^k*(bulkSize k L:ℝ))) →
      b ≤ Real.exp (-(F+67*(2:ℝ)^k*(bulkSize k L:ℝ))) →
      a+b ≤ Real.exp (-(F+65*(2:ℝ)^k*(bulkSize k L:ℝ))) := by
  filter_upwards [(bulkSize_tendsto_atTop hk).eventually_ge_atTop 1] with L hm
  intro F a b ha hb
  exact two_terms_exp_67_65_le k hm ha hb

theorem eventually_norm_add_exp_67_65_le {k : ℕ} (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop, ∀ F : ℝ, ∀ z w : ℂ,
      ‖z‖ ≤ Real.exp (-(F+67*(2:ℝ)^k*(bulkSize k L:ℝ))) →
      ‖w‖ ≤ Real.exp (-(F+67*(2:ℝ)^k*(bulkSize k L:ℝ))) →
      ‖z+w‖ ≤ Real.exp (-(F+65*(2:ℝ)^k*(bulkSize k L:ℝ))) := by
  filter_upwards [(bulkSize_tendsto_atTop hk).eventually_ge_atTop 1] with L hm
  intro F z w hz hw
  exact norm_add_exp_67_65_le k hm z w hz hw

end Ostmann.Arithmetic.HistoryActualComparisonDecayArithmetic

end

end OAI
