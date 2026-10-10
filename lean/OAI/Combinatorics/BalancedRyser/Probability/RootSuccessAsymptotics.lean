import Mathlib.Analysis.SpecialFunctions.Choose
import OAI.Combinatorics.BalancedRyser.Probability.RootSuccess

namespace OAI

namespace Balanced.TupleAlignment

open Filter Topology
open scoped BigOperators

private theorem rootMomentRatio_tendsto :
    Tendsto (fun q : ℕ => 16 * ((q.descFactorial 4 : ℝ) / (q : ℝ)^4)^2)
      atTop (𝓝 16) := by
  have hne : ∀ᶠ q : ℕ in atTop, (q : ℝ)^4 ≠ 0 := by
    filter_upwards [eventually_ge_atTop 1] with q hq
    have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
    exact pow_ne_zero _ hq0
  have h := (Asymptotics.isEquivalent_iff_tendsto_one hne).mp
    (isEquivalent_descFactorial 4)
  have hc : Tendsto (fun _ : ℕ => (16 : ℝ)) atTop (𝓝 16) := tendsto_const_nhds
  simpa only [one_pow, mul_one, Pi.div_apply] using hc.mul (h.pow 2)

theorem mean_rootSuccessCount_asymptotic
    (F : ℕ → Type*) [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)] (g : ∀ n, Direction (F n))
    (hcard : Tendsto (fun n => Fintype.card (F n)) atTop atTop) :
    Tendsto (fun n =>
      ((∑ M : MergedPairs (F n), (rootSuccessCount (g n) M : ℝ)) /
        Fintype.card (MergedPairs (F n))) / Fintype.card (F n))
      atTop (𝓝 16) := by
  classical
  have h := rootMomentRatio_tendsto.comp hcard
  apply h.congr'
  filter_upwards [] with n
  rw [mean_rootSuccessCount]
  have hq : (Fintype.card (F n) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  dsimp only [Function.comp_def]
  field_simp

end Balanced.TupleAlignment

end OAI
