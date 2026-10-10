import OAI.NumberTheory.EgyptianFractions.CompositeBadDensity
import OAI.NumberTheory.EgyptianFractions.RoughModulusBlocks

namespace OAI
noncomputable section
open Filter

namespace Problem337.CompositeSupply
local instance : DecidablePred BadModulus := Classical.decPred _

lemma base_eq_thinSupplyBase (u : ℕ) :
    base u = thinSupplyBase (2 / Real.log 2) u := by
  unfold base thinSupplyBase
  rw [primeCount_eq_supplyPrimeCount]

/-- The variable-pool global exception set embeds into the actual fixed-pool
exception block. Both roughness and the energy threshold follow from its
definition and the proved unit-mixing contraction. -/
theorem badModuli_block_subset (D : ℕ) (hD : 2 ≤ D) :
    (Finset.Ico D (2 * D)).filter BadModulus ⊆ roughModulusBadBlock D := by
  classical
  intro d hd
  obtain ⟨hdI, hbad⟩ := Finset.mem_filter.mp hd
  have hdD : D ≤ d := (Finset.mem_Ico.mp hdI).1
  let : NeZero d := ⟨by omega⟩
  change d ∈ (Finset.Ico D (2 * D)).filter _
  refine Finset.mem_filter.mpr ⟨hdI, ?_, ?_⟩
  · intro p hp
    exact badModulus_prime_lower hD hdD hbad
      (Nat.prime_of_mem_primeFactorsList hp) (Nat.dvd_of_mem_primeFactorsList hp)
  · simpa only [← base_eq_thinSupplyBase] using
      badModulus_fixed_base_collisions (by omega : 0 < D) hdD hbad

/-- An unconditional sparse dyadic count for one global predicate. No
unproved rough-divisor, collision, or distribution hypothesis remains. -/
theorem eventually_badModulus_shell_card_le :
    ∀ᶠ j : ℕ in atTop,
      (((Finset.Ico (2 ^ j) (2 ^ (j + 1))).filter BadModulus).card : ℝ) ≤
        ((2 : ℝ) ^ j) ^ (15 / 16 : ℝ) := by
  classical
  obtain ⟨D₀, hD₀⟩ := eventually_atTop.mp eventually_roughModulusBadBlock_card_le
  filter_upwards [eventually_ge_atTop (max D₀ 2)] with j hj
  have hjpow : j ≤ 2 ^ j := Nat.le_of_lt (Nat.lt_two_pow_self (n := j))
  have hpowD : D₀ ≤ 2 ^ j := ((le_max_left D₀ 2).trans hj).trans hjpow
  have hpow2 : 2 ≤ 2 ^ j := ((le_max_right D₀ 2).trans hj).trans hjpow
  have hsub := badModuli_block_subset (2 ^ j) hpow2
  have hcard : (((Finset.Ico (2 ^ j) (2 ^ (j + 1))).filter BadModulus).card : ℝ) ≤
      ((roughModulusBadBlock (2 ^ j)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (by simpa [pow_succ, Nat.mul_comm] using hsub)
  exact hcard.trans (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hD₀ _ hpowD)

/-- The exceptional original integers have arbitrarily small density.
This is the unconditional arithmetic input for the cube-free supply assembly. -/
theorem eventually_badMultiples_card_le :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ Y : ℕ in atTop,
      ((badMultiples Y).card : ℝ) ≤ ε * Y := by
  apply eventually_badMultiples_card_le_of_shell_bound
    (C := 1) (β := 15 / 16) (by norm_num) (by norm_num)
  simpa only [one_mul] using eventually_badModulus_shell_card_le

end Problem337.CompositeSupply

end

end OAI
