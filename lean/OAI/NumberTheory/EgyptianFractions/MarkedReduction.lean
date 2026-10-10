import OAI.NumberTheory.EgyptianFractions.MarkedConstruction
import OAI.NumberTheory.EgyptianFractions.MarkedQuantitative

namespace OAI
noncomputable section

open scoped BigOperators
open Filter

namespace Problem337

/-- The precise portion of the marked greedy-prefix output used by the final
construction.  The marker is not included in `p`; it is inserted afterwards. -/
def HasQuantitativeMarkedPrefix (m K : ℕ) : Prop :=
  ∃ p : Finset ℕ, ∃ q R : ℕ,
    0 < q ∧ R < 2 * m ∧ R * K ≤ q ∧ HasMarkedDivisorDensity m q ∧
    (∀ d ∈ p, 1 ≤ d) ∧ m ∉ p ∧
    ((1 : ℚ) / (m : ℚ) + ∑ d ∈ p, (1 : ℚ) / (d : ℚ)) +
      (R : ℚ) / (q : ℚ) = 1 ∧
    (∀ d ∈ insert m p, (R : ℚ) / (q : ℚ) < 1 / (d : ℚ)) ∧
    (p.card : ℝ) ≤ 3 + (Real.log (Real.log (2 * (m : ℝ) * (K : ℝ))) -
      Real.log (Real.log 2)) / Real.log 2

/-- Full quantitative endgame: a rational-divisor supply with a logarithmic
size estimate and the marked greedy prefix imply the `257 / log 2 + ε` bound.
Both remaining construction inputs are exposed explicitly. -/
theorem quantitative_marked_length_of_supply_and_prefix (K : ℕ → ℕ)
    (hKpositive : ∀ᶠ m : ℕ in atTop, 0 < K m)
    (hsize : ∀ δ : ℝ, 0 < δ → ∀ᶠ m : ℕ in atTop,
      Real.log (K m : ℝ) ≤ (32 / Real.log 2 + δ) * Real.log (m : ℝ) *
        Real.log (Real.log (m : ℝ)))
    (hsupply : ∀ᶠ m : ℕ in atTop, HasRationalDivisorSupply m (K m) 16)
    (hprefix : ∀ᶠ m : ℕ in atTop, HasQuantitativeMarkedPrefix m (K m)) :
    ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, 2 ≤ M ∧
      ∀ m : ℕ, M ≤ m → ∃ k : ℕ, ∃ n : Fin k → ℕ,
        IsOneExpansion n ∧ (∃ i, n i = m) ∧
        (k : ℝ) ≤ (257 / Real.log 2 + ε) * Real.log (Real.log (m : ℝ)) := by
  apply quantitative_marked_length_of_explicit_budget (fun m => (K m : ℝ))
  · filter_upwards [hKpositive] with m hm
    exact_mod_cast hm
  · exact hsize
  · filter_upwards [hKpositive, hsupply, hprefix, eventually_ge_atTop (2 : ℕ)]
      with m hKpositive hsupply hprefix hm
    obtain ⟨p, q, R, hq, hR, hRKq, hdensity, hp, hmarker, hsum, hsmall, hlength⟩ := hprefix
    have hp' : ∀ d ∈ insert m p, 1 ≤ d := by
      intro d hd
      rcases Finset.mem_insert.1 hd with rfl | hd
      · omega
      · exact hp d hd
    have hsum' : (∑ d ∈ insert m p, (1 : ℚ) / (d : ℚ)) + (R : ℚ) / (q : ℚ) = 1 := by
      rw [Finset.sum_insert hmarker]
      exact hsum
    obtain ⟨t, k, n, hk, hn, hnm, ht⟩ :=
      marked_expansion_from_rational_supply m q (K m) R (insert m p) hm hq hKpositive
        hR hRKq hdensity hsupply hp' (Finset.mem_insert_self m p) hsum' hsmall
    refine ⟨p.card, t, k, n, hn, hnm, ?_, hlength, ht⟩
    rw [Finset.card_insert_of_notMem hmarker] at hk
    omega

end Problem337

end

end OAI
