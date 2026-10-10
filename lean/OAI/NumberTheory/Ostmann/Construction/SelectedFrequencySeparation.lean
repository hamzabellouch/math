import OAI.NumberTheory.Ostmann.Construction.ScheduledPrimeCutoffs

namespace OAI

/-! # Uniform frequency separation below the two actual prime bands -/
namespace Ostmann
open Filter

theorem eventual_selected_frequency_separation (k : ℕ) (Bs BD Bz : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ (V : ℕ → ℕ) (G : ℝ),
      (∀ n ≤ k, (V n : ℝ) ≤
        Real.exp (movingFrequencyRate (Bs + 1) (BD + 2) Bz ((k : ℝ) ^ 4) n *
          spectatorBulkCount k L)) →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ G - 1 →
      ∀ n ≤ k, (V n : ℝ) < Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ∧
        (V n : ℝ) < Real.exp (G - 1) := by
  filter_upwards [eventual_selected_frequency_band k Bs BD Bz (39 / 10000) (by norm_num),
    eventually_ge_atTop (0 : ℝ)] with L hfreq hL
  intro V G hV hG n hn
  have hf := hfreq n hn V (hV n hn)
  refine ⟨hf, hf.trans_le ?_⟩
  apply Real.exp_le_exp.mpr
  apply le_trans _ hG
  apply Real.exp_le_exp.mpr
  nlinarith only [hL]

end Ostmann

end OAI
