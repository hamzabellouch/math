import OAI.NumberTheory.EgyptianFractions.ResidueStep

namespace OAI
open scoped BigOperators

namespace Problem337.Descent

/-- Length-bounded positive unit-fraction lists; repetitions are allowed at
this stage of the density construction. -/
def UnitListAtMost (x : ℚ) (B : ℕ) : Prop :=
  ∃ k : ℕ, k ≤ B ∧ ∃ n : Fin k → ℕ,
    (∀ i, 0 < n i) ∧ (∑ i : Fin k, (1 : ℚ) / (n i : ℚ)) = x

theorem UnitListAtMost.mono {x : ℚ} {B C : ℕ}
    (h : UnitListAtMost x B) (hBC : B ≤ C) : UnitListAtMost x C := by
  obtain ⟨k, hk, n, hn, hsum⟩ := h
  exact ⟨k, hk.trans hBC, n, hn, hsum⟩

theorem unitListAtMost_zero (B : ℕ) : UnitListAtMost 0 B := by
  refine ⟨0, Nat.zero_le _, Fin.elim0, ?_, ?_⟩
  · intro i; exact Fin.elim0 i
  · simp

theorem UnitListAtMost.change_factor {B M Q Qnext h : ℕ}
    (H : UnitListAtMost ((h : ℚ) / (M * Qnext : ℕ)) B)
    (hM : 0 < M) (hQ : 0 < Q) (hQnext : 0 < Qnext) (hdiv : Qnext ∣ Q) :
    UnitListAtMost ((h : ℚ) / (M * Q : ℕ)) B := by
  obtain ⟨k, hk, n, hn, hsum⟩ := H
  obtain ⟨n', hn', hsum'⟩ := unit_fraction_list_change_factor
    M Q Qnext h hM hQ hQnext hdiv n hn hsum
  exact ⟨k, hk, n', hn', hsum'⟩

theorem UnitListAtMost.residue_step {B M Q Qnext u t z h : ℕ}
    (H : UnitListAtMost ((h : ℚ) / (M * Qnext : ℕ)) B)
    (hM : 0 < M) (hQ : 0 < Q) (hQnext : 0 < Qnext)
    (ht : 0 < t) (hz : 0 < z) (htM : t ∣ M) (hdiv : Qnext ∣ Q)
    (hres : Q * t + h = u * z) :
    UnitListAtMost ((u : ℚ) / (M * Q : ℕ)) (B + 1) := by
  obtain ⟨k, hk, n, hn, hsum⟩ := H
  obtain ⟨n', hn', hsum'⟩ := residue_step_list_change_factor
    M Q Qnext u t z h hM hQ hQnext ht hz htM hdiv hres n hn hsum
  exact ⟨k + 1, Nat.add_le_add_right hk 1, n', hn', hsum'⟩

/-- Backward propagation of bounded expansions through good numerator sets.
The hypotheses encode exactly the inherited-membership and successful-residue
alternatives in the dense-family construction. -/
theorem backward_good_set_expansions
    (M d B : ℕ) (Q : ℕ → ℕ) (G : ℕ → Set ℕ)
    (hM : 0 < M) (hQ : ∀ j, j ≤ d → 0 < Q j)
    (hdiv : ∀ j, j < d → Q (j + 1) ∣ Q j)
    (hterminal : ∀ u ∈ G d,
      UnitListAtMost ((u : ℚ) / (M * Q d : ℕ)) B)
    (hstep : ∀ j, j < d → ∀ u ∈ G j,
      u ∈ G (j + 1) ∨ ∃ t z h : ℕ,
        0 < t ∧ t ∣ M ∧ 0 < z ∧ Q j * t + h = u * z ∧
          (h = 0 ∨ h ∈ G (j + 1))) :
    ∀ j, j ≤ d → ∀ u ∈ G j,
      UnitListAtMost ((u : ℚ) / (M * Q j : ℕ)) (B + (d - j)) := by
  intro j hj
  induction hj using Nat.decreasingInduction with
  | self =>
      intro u hu
      simpa using hterminal u hu
  | of_succ j hj ih =>
      intro u hu
      have hQj := hQ j (by omega)
      have hQnext := hQ (j + 1) (by omega)
      rcases hstep j hj u hu with hu' | ⟨t, z, h, ht, htM, hz, hres, hh⟩
      · exact ((ih u hu').change_factor hM hQj hQnext (hdiv j hj)).mono (by omega)
      · have H : UnitListAtMost ((h : ℚ) / (M * Q (j + 1) : ℕ))
            (B + (d - (j + 1))) := by
          rcases hh with rfl | hh
          · simpa using unitListAtMost_zero (B + (d - (j + 1)))
          · exact ih h hh
        exact (H.residue_step hM hQj hQnext ht hz htM (hdiv j hj) hres).mono (by omega)

/-- If a propagated fraction is below one, its positive denominators are
all at least two, as required by the dense-family interface. -/
theorem UnitListAtMost.denominators_two {x : ℚ} {B : ℕ}
    (H : UnitListAtMost x B) (hx : x < 1) :
    ∃ k : ℕ, k ≤ B ∧ ∃ n : Fin k → ℕ,
      (∀ i, 2 ≤ n i) ∧ (∑ i : Fin k, (1 : ℚ) / (n i : ℚ)) = x := by
  obtain ⟨k, hk, n, hn, hsum⟩ := H
  exact ⟨k, hk, n, unit_fraction_denominators_two_of_sum_lt_one n hn (hsum ▸ hx), hsum⟩

end Problem337.Descent

end OAI
