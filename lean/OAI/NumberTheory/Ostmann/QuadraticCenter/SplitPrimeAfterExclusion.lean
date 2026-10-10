import OAI.NumberTheory.Ostmann.QuadraticCenter.PageKernelExclusion
import OAI.NumberTheory.Ostmann.QuadraticCenter.SplitMassNumerics

namespace OAI

/-! # The split-prime bound after the explicit Page-family deletion -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def splitPrimeMassLower (P : PublishedProgressionInput)
    (H : PublishedRealZeroInput P) (A K C ε : ℝ) (Q₀ Q D Y : ℕ) (R s : ℝ) : ℝ :=
  (1 / (s - 1) - C -
    (2 * zeroComparisonConstant P * Real.log (4 * (Q₀ : ℝ)) +
      K * R ^ ε + H.errorConstant + A + 2)) / 2 -
    (Q : ℝ) ^ (-(s - 1) / 2) * (2 / (s - 1) + C) - (Y + Real.log D / Y)

/-- The Page condition is discharged using the finite, explicitly constructed
exclusion set. No exceptional-character identification is assumed. -/
theorem split_prime_mass_after_exclusion (P : PublishedProgressionInput)
    (H : PublishedRealZeroInput P) (hSiegel : PublishedSiegelBound)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ A K C : ℝ, 0 < A ∧ 0 < K ∧ 0 < C ∧
      ∀ (d : ℤ) (Q₀ Q D Y : ℕ) (R s : ℝ),
        Squarefree d.natAbs → 2 < d.natAbs →
        2 ≤ Q₀ → 4 * d.natAbs ≤ Q₀ → 0 < Q → 0 < D → 0 < Y →
        d.natAbs ∣ D → 0 ≤ R →
        2 * (A + H.errorConstant) ≤ Real.log (4 * (Q₀ : ℝ)) →
        1 < s → s ≤ 2 → s ≤ 1 + 1 / Real.log (4 * (Q₀ : ℝ)) →
        d ∉ pageKernelExclusion P Q₀ R →
        splitPrimeMassLower P H A K C ε Q₀ Q D Y R s ≤
          ∑ p ∈ (Nat.primesLE Q).filter (fun p => ¬p ∣ D ∧ jacobiSym d p = 1),
            Real.log p / (p : ℝ) := by
  obtain ⟨A, K, C, hA, hK, hC, hmass⟩ := retained_split_prime_mass P H hSiegel ε hε
  refine ⟨A, K, C, hA, hK, hC, ?_⟩
  intro d Q₀ Q D Y R s hsf hd hQ₀ hdQ₀ hQ hD hY hdD hR hsize hs hs2 hss hout
  obtain ⟨χ, N, hN, hNq, hqN, hdN, hqd, _, hbound⟩ := hmass d hsf hd
  apply hbound Q₀ Q D Y R s hQ₀ hdQ₀ hQ hD hY hdD hR hsize hs hs2 hss
  exact page_kernel_retention P Q₀ R d χ N (by omega) hNq hqN hdN hqd hout

end Ostmann

end OAI
