import OAI.NumberTheory.EgyptianFractions.RationalSupplyReduction

namespace OAI
noncomputable section
open scoped BigOperators
open Filter

namespace Problem337

/-- The logarithmically weighted ordered prime triple count, with exactly the
same triples as the rational-divisor supply reduction. -/
def weightedSupplyPrimeTriples (u : ℕ) : ℝ :=
  ∑ t ∈ supplyPrimeTriples u,
    Real.log (t.1 : ℝ) * Real.log (t.2.1 : ℝ) * Real.log (t.2.2 : ℝ)

lemma weightedSupplyPrimeTriples_le (u : ℕ) :
    weightedSupplyPrimeTriples u ≤
      (supplyPrimeTriples u).card * Real.log (u : ℝ) ^ 3 := by
  unfold weightedSupplyPrimeTriples
  calc
    _ ≤ ∑ _t ∈ supplyPrimeTriples u, Real.log (u : ℝ) ^ 3 := by
      apply Finset.sum_le_sum
      intro t ht
      obtain ⟨htmem, htprime⟩ := Finset.mem_filter.mp ht
      obtain ⟨hp, hq, hr⟩ := Finset.mem_product.mp htmem |>.imp_right Finset.mem_product.mp
      have hlog (p : ℕ) (hp : p ∈ Finset.Icc 1 u) :
          0 ≤ Real.log (p : ℝ) ∧ Real.log (p : ℝ) ≤ Real.log (u : ℝ) := by
        obtain ⟨hp1, hpu⟩ := Finset.mem_Icc.mp hp
        have hp1r : (1 : ℝ) ≤ p := by exact_mod_cast hp1
        exact ⟨Real.log_nonneg hp1r,
          Real.log_le_log (lt_of_lt_of_le zero_lt_one hp1r) (by exact_mod_cast hpu)⟩
      obtain ⟨hp0, hpu⟩ := hlog t.1 hp
      obtain ⟨hq0, hqu⟩ := hlog t.2.1 hq
      obtain ⟨hr0, hru⟩ := hlog t.2.2 hr
      have hu0 : 0 ≤ Real.log (u : ℝ) := hp0.trans hpu
      calc
        _ ≤ (Real.log (u : ℝ) * Real.log (u : ℝ)) * Real.log (u : ℝ) :=
          mul_le_mul (mul_le_mul hpu hqu hq0 hu0) hru hr0 (by positivity)
        _ = _ := by ring
    _ = _ := by simp

/-- Positive quadratic logarithmically weighted count is enough for the
precise unweighted lower-bound interface already used by the solution. -/
theorem quantitativeThreePrimeLowerBound_of_weighted
    (hweighted : ∃ c : ℝ, 0 < c ∧ ∀ᶠ u : ℕ in atTop, Odd u →
      c * (u : ℝ) ^ 2 ≤ weightedSupplyPrimeTriples u) :
    QuantitativeThreePrimeLowerBound := by
  obtain ⟨c, hc, hw⟩ := hweighted
  refine ⟨c, hc, ?_⟩
  filter_upwards [hw, eventually_ge_atTop 2] with u hu hu2
  intro hodd
  have hur : (1 : ℝ) < u := by exact_mod_cast (show 1 < u by omega)
  have hlog : 0 < Real.log (u : ℝ) ^ 3 := pow_pos (Real.log_pos hur) 3
  have h := (hu hodd).trans (weightedSupplyPrimeTriples_le u)
  rw [← mul_div_assoc]
  exact (div_le_iff₀ hlog).2 h

end Problem337

end

end OAI
