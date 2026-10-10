import OAI.NumberTheory.EgyptianFractions.RationalDivisorSupplyAlgebra
import OAI.NumberTheory.EgyptianFractions.MarkedGroupingUnits

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- Convert the finite-indexed supply API to the list API consumed by grouping. -/
theorem HasRationalDivisorSum.to_list {K B : ℕ} {x : ℚ}
    (h : HasRationalDivisorSum K x B) :
    ∃ terms : List (ℕ × ℕ), terms.length ≤ B ∧
      (∀ et ∈ terms, 0 < et.1 ∧ et.1 ∣ K ∧ 0 < et.2) ∧
      (terms.map (fun et => (et.1 : ℚ) / (et.2 : ℚ))).sum = x := by
  obtain ⟨k, hk, e, t, het, hsum⟩ := h
  refine ⟨List.ofFn (fun i => (e i, t i)), by simpa using hk, ?_, ?_⟩
  · intro et hmem
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hmem
    exact het i
  · simpa only [List.map_ofFn, List.sum_ofFn, Function.comp_apply] using hsum

/-- The algebraic odd-integer supply interface directly feeds the canonical
unit-fraction grouping construction. -/
theorem rational_divisor_supply_bridge {m K B : ℕ}
    (h : ∀ s : ℕ, 1 ≤ s → s ≤ m ^ 4 → HasRationalDivisorSum K (s : ℚ) B) :
    HasRationalDivisorSupply m K B := by
  intro s hs hsm
  exact (h s hs hsm).to_list

theorem rational_divisor_supply_from_odd {m K N : ℕ} (hN : 1 ≤ N)
    (hNK : N.factorial ∣ K)
    (hodd : ∀ u : ℕ, N ≤ u → u ≤ m ^ 4 → Odd u →
      HasRationalDivisorSum K (u : ℚ) 15) :
    HasRationalDivisorSupply m K 16 :=
  rational_divisor_supply_bridge (rational_divisor_supply_of_odd hN hNK hodd)

theorem rational_divisor_supply_from_triples {m K N : ℕ} (hN : 1 ≤ N)
    (hNK : N.factorial ∣ K)
    (htriples : ∀ u : ℕ, N ≤ u → u ≤ m ^ 4 → Odd u →
      ∃ p q r : ℕ, p + q + r = u ∧
        HasRationalDivisorSum K (p : ℚ) 5 ∧
        HasRationalDivisorSum K (q : ℚ) 5 ∧
        HasRationalDivisorSum K (r : ℚ) 5) :
    HasRationalDivisorSupply m K 16 :=
  rational_divisor_supply_bridge (rational_divisor_supply_of_triples hN hNK htriples)

/-- Eventual form convenient for the quantitative marked-length reduction. -/
theorem eventually_rational_divisor_supply_from_odd (K : ℕ → ℕ) {N : ℕ}
    (hN : 1 ≤ N) (hfactorial : ∀ᶠ m : ℕ in Filter.atTop, N.factorial ∣ K m)
    (hodd : ∀ᶠ m : ℕ in Filter.atTop, ∀ u : ℕ, N ≤ u → u ≤ m ^ 4 → Odd u →
      HasRationalDivisorSum (K m) (u : ℚ) 15) :
    ∀ᶠ m : ℕ in Filter.atTop, HasRationalDivisorSupply m (K m) 16 := by
  filter_upwards [hfactorial, hodd] with m hfm hom
  exact rational_divisor_supply_from_odd hN hfm hom

end Problem337

end

end OAI
