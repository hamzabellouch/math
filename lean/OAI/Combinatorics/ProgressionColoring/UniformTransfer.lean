import OAI.Combinatorics.ProgressionColoring.DigitProductBounds
import OAI.Combinatorics.ProgressionColoring.GrowthConsequences

namespace OAI

namespace QuantitativeVanDerWaerden

open Filter

/-- One threshold supplies actual avoiding cyclic colorings independently
of the eventual number of colors. This is a proposition, not an axiom. -/
def CyclicLowerBound (c : ℝ) : Prop :=
  ∃ K : ℕ, ∀ k ≥ K, ∃ N : ℕ,
    2 ≤ N ∧ (k : ℝ) ^ (c * k) ≤ (N : ℝ) ∧
      ∃ C : ZMod N → Bool, CyclicAvoids C k

/-- The same cyclic coloring works for every number of digits. -/
theorem uniform_lower_of_cyclicLowerBound {c : ℝ} (hcyclic : CyclicLowerBound c) :
    ∃ K : ℕ, ∀ k ≥ K, ∀ r ≥ 2,
      (k : ℝ) ^ (c * k * (Nat.log 2 r : ℝ)) < (W r k : ℝ) := by
  obtain ⟨K, hK⟩ := hcyclic
  refine ⟨max K 2, ?_⟩
  intro k hk r hr
  have hk2 : 2 ≤ k := (le_max_right K 2).trans hk
  obtain ⟨N, hN, hsize, C, hC⟩ := hK k ((le_max_left K 2).trans hk)
  have hprod := cyclic_binary_color_lower hN hk2 hr hC
  calc
    (k : ℝ) ^ (c * k * (Nat.log 2 r : ℝ)) =
        ((k : ℝ) ^ (c * k)) ^ Nat.log 2 r :=
      Real.rpow_mul_natCast (Nat.cast_nonneg k) _ _
    _ ≤ (N : ℝ) ^ Nat.log 2 r :=
      pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg k) _) hsize _
    _ < (W r k : ℝ) := by exact_mod_cast hprod

/-- The fixed-color full limit from a proved cyclic construction. -/
theorem kthRoot_tendsto_of_cyclicLowerBound {c : ℝ} (hc : 0 < c)
    (hcyclic : CyclicLowerBound c) {r : ℕ} (hr : 2 ≤ r) :
    Tendsto (fun k : ℕ => (W r k : ℝ) ^ (1 / (k : ℝ))) atTop atTop := by
  obtain ⟨K, hK⟩ := uniform_lower_of_cyclicLowerBound hcyclic
  exact fixed_color_kthRoot_tendsto (F := fun r k => (W r k : ℝ))
    (c := c) (K := K) (r := r) hc hK hr

/-- The infimum over all color counts retains one absolute threshold. -/
theorem length_rate_tendsto_of_cyclicLowerBound {c : ℝ} (hc : 0 < c)
    (hcyclic : CyclicLowerBound c) :
    Tendsto (fun k : ℕ => ⨅ r : {r : ℕ // 2 ≤ r},
      Real.log (W r.val k : ℝ) / ((k : ℝ) * Real.log (r.val : ℝ))) atTop atTop := by
  obtain ⟨K, hK⟩ := uniform_lower_of_cyclicLowerBound hcyclic
  exact uniform_length_rate_tendsto (F := fun r k => (W r k : ℝ))
    (c := c) (K := K) hc hK

end QuantitativeVanDerWaerden

end OAI
