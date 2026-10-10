import OAI.NumberTheory.Ostmann.Preliminaries.SummandSqrtLower
import OAI.NumberTheory.Ostmann.Preliminaries.PublishedSummandBounds

namespace OAI

/-! # The required summand-size theorem, without a published-input hypothesis

The proof uses the proved additive sieve and actual prime distribution. The
finite fixed-shift sieve gives logarithmic growth, exponential sampling gives
a concrete polynomial bootstrap, and the two-cutoff collision estimate gives
the final square-root bounds. This supplies the exact consequence recorded
from Elsholtz (2006), Theorem 1.9.
-/

namespace Ostmann

open Filter

 theorem publishedSummandSizeBound : PublishedSummandSizeBound := by
  intro A B hA hB h
  obtain ⟨aA, haA, hAl⟩ := h.summand_sqrt_lower hA
  obtain ⟨aB, haB, hBl⟩ := h.symm.summand_sqrt_lower hB
  obtain ⟨CA, hCA, hAu⟩ := h.summand_sqrt_upper hB
  obtain ⟨CB, hCB, hBu⟩ := h.symm.summand_sqrt_upper hA
  let a := min aA aB
  let C := max CA CB
  refine ⟨a, C, lt_min haA haB, lt_max_of_lt_left hCA, ?_⟩
  have hev : ∀ᶠ N : ℕ in atTop,
      a * Real.sqrt (N : ℝ) / Real.log (N : ℝ) ^ 3 ≤ (summandPrefix A N).card ∧
      (summandPrefix A N).card ≤ C * Real.sqrt (N : ℝ) * Real.log (N : ℝ) ^ 2 ∧
      a * Real.sqrt (N : ℝ) / Real.log (N : ℝ) ^ 3 ≤ (summandPrefix B N).card ∧
      (summandPrefix B N).card ≤ C * Real.sqrt (N : ℝ) * Real.log (N : ℝ) ^ 2 := by
    filter_upwards [hAl, hBl, hAu, hBu, eventually_ge_atTop (2 : ℕ)] with N hAl hBl hAu hBu hN
    have hl : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply le_trans ?_ hAl
      dsimp [a]
      gcongr
      exact min_le_left _ _
    · apply le_trans hAu
      dsimp [C]
      gcongr
      exact le_max_left _ _
    · apply le_trans ?_ hBl
      dsimp [a]
      gcongr
      exact min_le_right _ _
    · apply le_trans hBu
      dsimp [C]
      gcongr
      exact le_max_right _ _
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hev
  exact ⟨N₀, fun N hN _ => hN₀ N hN⟩

end Ostmann

end OAI
