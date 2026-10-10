import OAI.Combinatorics.MatrixRemoval.Model
import OAI.Combinatorics.MatrixRemoval.Asymptotics

namespace OAI

/-!
The sequence of matrix counterexamples rules out every polynomial
removal bound.
-/

noncomputable section

namespace Problem348

/-- Exponential decay of the copy density rules out polynomial removal bounds. -/
theorem no_polynomial_removal_bound_of_sequence
    (hseq : ∀ h : ℕ, 1 ≤ h →
      let d : ℕ := 386 * h + 2
      let n : ℕ := d * 2 ^ h
      ∃ A : BinaryMatrix n,
        fixedDistance A ≥ 1 / ((d : ℝ) ^ 2) ∧
        (copyCount fixedH A : ℝ) / ((n : ℝ) ^ 132) ≤
          (1 / ((d : ℝ) ^ 2)) * (1 / ((2 : ℝ) ^ h))) :
    ∀ c C : ℝ, 0 < c → 0 < C →
      ∃ n : ℕ, 1 ≤ n ∧
        ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
          ∃ A : BinaryMatrix n,
            fixedDistance A ≥ ε ∧
            (copyCount fixedH A : ℝ) <
              c * Real.rpow ε C * ((n : ℝ) ^ 132) := by
  intro c C hc _hC
  obtain ⟨h, hh, hdecay⟩ := exists_depth_polynomial_decay c C hc
  let d : ℕ := 386 * h + 2
  let n : ℕ := d * 2 ^ h
  have hd : 1 < d := by dsimp [d]; omega
  have hdR : (1 : ℝ) < d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hn : 0 < n := Nat.mul_pos (by omega) (pow_pos (by decide) _)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨A, hdist, hcopies⟩ := hseq h hh
  refine ⟨n, hn, 1 / ((d : ℝ) ^ 2), by positivity, ?_, A, hdist, ?_⟩
  · apply (div_lt_one (by positivity)).2
    nlinarith
  · have hdecay' : (1 / ((d : ℝ) ^ 2)) * (1 / ((2 : ℝ) ^ h)) <
        c * Real.rpow (1 / ((d : ℝ) ^ 2)) C := by
      simpa [d] using hdecay
    exact (div_lt_iff₀ (pow_pos hnR 132)).mp (hcopies.trans_lt hdecay')

end Problem348

end

end OAI
