import OAI.Combinatorics.BalancedRyser.Incidence.AffineInjectionGuards
import OAI.Combinatorics.BalancedRyser.Local.Local
import OAI.Combinatorics.BalancedRyser.Local.LocalAsymptotics

namespace OAI

open Filter
open scoped Topology

namespace Balanced.LocalAsymptotics

theorem eventually_mul_ceil_log_le (c : ℕ) :
    ∀ᶠ q : ℕ in atTop, c * ⌈Real.log (q : ℝ)⌉₊ ≤ q := by
  have hlim : Tendsto (fun q : ℕ =>
      (c : ℝ) * (⌈Real.log (q : ℝ)⌉₊ : ℝ) / (q : ℝ)) atTop (𝓝 0) := by
    simpa only [pow_one, mul_div_assoc, Function.comp_def, mul_zero] using
      ((tendsto_ceil_log_pow_div 1).comp tendsto_natCast_atTop_atTop).const_mul (c : ℝ)
  filter_upwards [hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_gt_atTop (0 : ℕ)] with q hq hpos
  have hqr : (0 : ℝ) < q := by exact_mod_cast hpos
  have hbound : (c : ℝ) * (⌈Real.log (q : ℝ)⌉₊ : ℝ) ≤ q :=
    ((div_lt_one hqr).mp hq).le
  exact_mod_cast hbound

end Balanced.LocalAsymptotics

namespace Balanced.Local

universe u

theorem exists_logBudget_token_threshold :
    ∃ q₀ : ℕ, ∀ (F : Type u) [Fintype F], q₀ ≤ Fintype.card F →
      ∀ b : ℕ, b ≤ logBudget F → 10 * b ≤ Fintype.card F := by
  obtain ⟨q₀, hq₀⟩ := Filter.eventually_atTop.mp
    (LocalAsymptotics.eventually_mul_ceil_log_le 10)
  refine ⟨q₀, ?_⟩
  intro F _ hF b hb
  exact (Nat.mul_le_mul_left 10 hb).trans (hq₀ (Fintype.card F) hF)

end Balanced.Local

end OAI
