import OAI.NumberTheory.Ostmann.Preliminaries.FixedShiftCount

namespace OAI

/-! # Every fixed logarithmic saving for an infinite summand -/

namespace Ostmann

open Filter

 theorem EventuallyPrimeSumset.summand_logarithmic_upper {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) (hB : B.Infinite) (j : ℕ) (hj : 1 ≤ j) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ((summandPrefix A N).card : ℝ) ≤ C * N / Real.log (N : ℝ) ^ j := by
  obtain ⟨T, hTB, hcard⟩ := hB.exists_subset_card_eq j
  have hT : T.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨N₀, hN⟩ := h.prime_add
  obtain ⟨C, hC, hbound⟩ := fixed_shift_count T hT A N₀ (by
    intro a ha hNa b hb
    exact hN a ha b (hTB hb) (by omega))
  refine ⟨C, hC, ?_⟩
  simpa only [hcard] using hbound

end Ostmann

end OAI
