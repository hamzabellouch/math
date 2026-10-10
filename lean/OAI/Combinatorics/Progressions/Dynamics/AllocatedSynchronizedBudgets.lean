import OAI.Combinatorics.Progressions.Estimates.PreparedCanonicalNativeSource

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]

theorem allocatedCanonicalSmoothingLog_eq_common (dim : ℕ) (p P E : ℝ) (A T : ℝ≥0) :
    allocatedCanonicalSmoothingLog B dim p P E A T = allocatedCommonSmoothingLog B dim A T p P E := by
  simp only [allocatedCanonicalSmoothingLog, allocatedCommonSmoothingLog, allocatedSiteKernelMaskLog,
    show E + 2 = E + 1 + 1 by ring]

theorem allocatedCanonicalTailLog_eq_common (dim : ℕ) (p P E : ℝ) (A T : ℝ≥0) :
    allocatedCanonicalTailLog (G := G) B dim p P E A T = allocatedCommonTailLog (G := G) B dim A T p P E := by
  simp only [allocatedCanonicalTailLog, allocatedCommonTailLog, allocatedSiteKernelMaskLog,
    show E + 2 = E + 1 + 1 by ring]

theorem exists_allocatedSynchronizedRegularizationLog_bound (m : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {G : Type} [Fintype G] {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
        (B : LayerSamplerAxis I n → Type) [∀ i, Fintype (B i)] (A T : ℝ≥0)
        {p P E : ℝ}, 0 ≤ p → 0 ≤ P → 0 ≤ E →
        (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p →
        (∀ j, (Fintype.card (I j) : ℝ) ≤ p) → (∀ j, (n j : ℝ) ≤ p) →
        (∑ s : Fin (m + 1), allocatedCanonicalSmoothingLog B (s.val + 1) p P E A T) ≤
          (p + A + T + P + E + C) ^ C ∧
        (∑ s : Fin (m + 1), allocatedCanonicalTailLog (G := G) B (s.val + 1) p P E A T) ≤
          (p + A + T + P + E + C) ^ C := by
  have hs (s : Fin (m + 1)) := exists_allocatedCommonRegularizationLog_bound.{0,0,0}
    m (s.val + 1)
  choose a ha hbound using hs
  let poly : Polynomial ℕ := ∑ s : Fin (m + 1), (Polynomial.X + Polynomial.C (a s)) ^ (a s)
  obtain ⟨C, hC, hpoly⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨C, hC, ?_⟩
  intro G _ I _ n B _ A T p P E hp hP hE hvars hI hn
  have hfinal : (∑ s : Fin (m + 1), (p + A + T + P + E + (a s : ℝ)) ^ a s) ≤
      (p + A + T + P + E + C) ^ C := by
    simpa [poly, Polynomial.eval₂_finsetSum, Polynomial.eval₂_pow] using
      hpoly (p + A + T + P + E) (by positivity)
  have hlogs (s : Fin (m + 1)) :=
    hbound s B A T hp hP hE (Nat.succ_le_of_lt s.isLt) hvars hI hn
  constructor
  · apply le_trans (Finset.sum_le_sum (fun s _ => ?_)) hfinal
    rw [allocatedCanonicalSmoothingLog_eq_common]
    exact (hlogs s).1
  · apply le_trans (Finset.sum_le_sum (fun s _ => ?_)) hfinal
    rw [allocatedCanonicalTailLog_eq_common]
    exact (hlogs s).2

end Erdos3.VectorPolynomial

end

end OAI
