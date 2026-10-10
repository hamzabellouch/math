import OAI.NumberTheory.EgyptianFractions.CompositeBadModuli
import OAI.NumberTheory.EgyptianFractions.SparseBadDivisorTail

namespace OAI
noncomputable section
open Filter
open scoped BigOperators

namespace Problem337.CompositeSupply
local instance : DecidablePred BadModulus := Classical.decPred _

/-- Integers containing a global bad conductor above the logarithmic cutoff.
This finite set depends only on the ambient range, not on any chosen modulus. -/
def badMultiples (Y : ℕ) : Finset ℕ := by
  classical
  exact SparseBadDivisorTail.divisorMultiples
    ((Finset.Icc ⌊Real.log (Y : ℝ)⌋₊ Y).filter BadModulus) Y

lemma mem_badMultiples_iff (Y n : ℕ) :
    n ∈ badMultiples Y ↔ 1 ≤ n ∧ n ≤ Y ∧
      ∃ d : ℕ, ⌊Real.log (Y : ℝ)⌋₊ ≤ d ∧ BadModulus d ∧ d ∣ n := by
  classical
  exact SparseBadDivisorTail.mem_divisorMultiples_badAbove
    BadModulus ⌊Real.log (Y : ℝ)⌋₊ Y n

/-- Every conductor of a residual modulus avoids the global bad set if
its original positive multiple avoids `badMultiples`. -/
lemma not_bad_of_not_mem_badMultiples {Y n q d : ℕ}
    (hn : 1 ≤ n) (hnY : n ≤ Y) (hqn : q ∣ n)
    (hc : (base Y).Coprime q) (hne : n ∉ badMultiples Y)
    (hdq : d ∣ q) (hd : 2 ≤ d) : ¬ BadModulus d := by
  intro hb
  have hlog := log_le_conductor hc hdq hd
  have hfloor : ⌊Real.log (Y : ℝ)⌋₊ ≤ d := by
    have hh := (Nat.floor_le (Real.log_natCast_nonneg Y)).trans hlog
    exact_mod_cast hh
  exact hne ((mem_badMultiples_iff Y n).mpr
    ⟨hn, hnY, d, hfloor, hb, hdq.trans hqn⟩)

/-- Quantitative conductor collisions for the global divisor pool, uniformly
for every residual divisor of an integer outside the one exceptional set. -/
lemma ambient_collisions_le_of_not_mem_badMultiples {Y n q d : ℕ} [NeZero d]
    (hn : 1 ≤ n) (hnY : n ≤ Y) (hqn : q ∣ n)
    (hc : (base Y).Coprime q) (hne : n ∉ badMultiples Y)
    (hdq : d ∣ q) (hd : 2 ≤ d) :
    ((collisionPairs (base Y).divisors (fun a => a % d)).card : ℝ) ≤
      ((base Y).divisors.card : ℝ)^2 / (d : ℝ)^(7 / 8 : ℝ) := by
  have hq : 0 < q := Nat.pos_of_dvd_of_pos hqn (by omega)
  exact ambient_collisions_le_of_not_bad hq
    ((Nat.le_of_dvd (by omega : 0 < n) hqn).trans hnY) hdq hc
    (not_bad_of_not_mem_badMultiples hn hnY hqn hc hne hdq hd) hd

/-- A sublinear shell count gives a vanishing exceptional-multiple density
at the actual logarithmic conductor cutoff. The shell hypothesis is the
only input; the cutoff and the product-energy transport are unconditional. -/
theorem eventually_badMultiples_card_le_of_shell_bound
    {C β : ℝ} (hC : 0 ≤ C) (hβ : β < 1)
    (hcount : ∀ᶠ j : ℕ in atTop,
      (((Finset.Ico (2 ^ j) (2 ^ (j + 1))).filter BadModulus).card : ℝ) ≤
        C * ((2 : ℝ) ^ j) ^ β) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ Y : ℕ in atTop,
      ((badMultiples Y).card : ℝ) ≤ ε * Y := by
  classical
  intro ε hε
  obtain ⟨J, hJ⟩ := eventually_atTop.mp hcount
  obtain ⟨R, hR, hbound⟩ :=
    SparseBadDivisorTail.eventually_large_bad_divisor_multiples_small
      BadModulus J hC hβ hJ ε hε
  have hlog : Tendsto (fun Y : ℕ => Real.log (Y : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually_ge_atTop (R : ℝ)] with Y hY
  have hfloor : R ≤ ⌊Real.log (Y : ℝ)⌋₊ := Nat.le_floor hY
  exact hbound _ hfloor Y

end Problem337.CompositeSupply

end

end OAI
