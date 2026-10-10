import OAI.NumberTheory.TotientAsymptotic.PrefixGeometry

namespace OAI

/-! Propagating the first discrete tail coordinate through the prefix. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

/-- The renewal recurrence propagates any terminal lower bound through the
triangular prefix inequalities. This includes the first discrete tail prime. -/
theorem renewal_prefix_lower (N : ℕ) (u : ℕ → ℝ)
    (hs : ∀ i < N, (∑ j ∈ Finset.Icc (i+1) N, a (j-i)*u j) ≤ u i)
    {i : ℕ} (hi : i ≤ N) : g (N-i)*u N ≤ u i := by
  have hmain : ∀ d : ℕ, ∀ j : ℕ, j+d=N → g d*u N ≤ u j := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro j hj
      by_cases hd : d = 0
      · subst d
        have hjN : j = N := by omega
        simp [hjN, g]
      · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
        have hrec := g_convolution hdpos
        calc
          g d*u N = ∑ r ∈ Finset.range d, a (d-r)*(g r*u N) := by
            rw [hrec, Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro r hr
            ring
          _ ≤ ∑ r ∈ Finset.range d, a (d-r)*u (N-r) := by
            apply Finset.sum_le_sum
            intro r hr
            have hrd := Finset.mem_range.mp hr
            apply mul_le_mul_of_nonneg_left
              (ih r hrd (N-r) (by omega)) (a_pos (by omega)).le
          _ = ∑ k ∈ Finset.Icc (j+1) N, a (k-j)*u k := by
            apply Finset.sum_bij (fun r _ => N-r)
            · intro r hr
              have := Finset.mem_range.mp hr
              exact Finset.mem_Icc.mpr (by omega)
            · intro r hr s hs hrs
              have := Finset.mem_range.mp hr
              have := Finset.mem_range.mp hs
              omega
            · intro k hk
              have := Finset.mem_Icc.mp hk
              exact ⟨N-k, Finset.mem_range.mpr (by omega), by omega⟩
            · intro r hr
              have := Finset.mem_range.mp hr
              congr 2
              omega
          _ ≤ u j := hs j (by omega)
  exact hmain (N-i) i (Nat.add_sub_of_le hi)

end TotientAsymptotic

end

end OAI
