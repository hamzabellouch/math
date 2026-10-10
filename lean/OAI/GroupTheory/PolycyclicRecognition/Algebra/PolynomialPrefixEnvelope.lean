import OAI.GroupTheory.PolycyclicRecognition.Algebra.BoundedPrefixEnvelope

namespace OAI

/-! # Polynomial losses preserve the common vanishing prefix envelope -/

namespace PolycyclicRecognition

open Filter
open scoped Topology

/-- The fixed polynomial loss in nilpotent multiplication only changes the
vanishing error exponent. The bound holds at every scale, not just eventually. -/
theorem exists_polynomial_exponential_envelope
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (hscale1 : ∀ n, 1 ≤ scale n)
    (ε : ℕ → ℝ) (hε0 : ∀ n, 0 ≤ ε n) (hε : Tendsto ε atTop (𝓝 0))
    (D : ℝ) (hD : 0 ≤ D) (d : ℕ) :
    ∃ η : ℕ → ℝ, (∀ n, 0 ≤ η n) ∧ Tendsto η atTop (𝓝 0) ∧
      ∀ n, D * (1 + Real.exp (scale n * ε n)) ^ d ≤ Real.exp (scale n * η n) := by
  obtain ⟨ζ, hζ0, hζ, hconst⟩ := exists_vanishing_exponential_envelope
    scale hscale hscale1 (D * 2 ^ d)
  let η := fun n => (d : ℝ) * ε n + ζ n
  refine ⟨η, fun n => add_nonneg (mul_nonneg (Nat.cast_nonneg _) (hε0 n)) (hζ0 n), ?_, ?_⟩
  · simpa only [mul_zero, zero_add] using (tendsto_const_nhds.mul hε).add hζ
  · intro n
    have hr : 0 ≤ scale n := le_trans (by norm_num) (hscale1 n)
    have he : 1 ≤ Real.exp (scale n * ε n) :=
      Real.one_le_exp_iff.mpr (mul_nonneg hr (hε0 n))
    calc
      D * (1 + Real.exp (scale n * ε n)) ^ d ≤
          D * (2 * Real.exp (scale n * ε n)) ^ d := by gcongr; linarith
      _ = (D * 2 ^ d) * Real.exp ((d : ℝ) * (scale n * ε n)) := by
        rw [mul_pow, Real.exp_nat_mul]
        ring
      _ ≤ Real.exp (scale n * ζ n) * Real.exp ((d : ℝ) * (scale n * ε n)) :=
        mul_le_mul_of_nonneg_right (hconst n) (Real.exp_pos _).le
      _ = Real.exp (scale n * η n) := by
        rw [← Real.exp_add]
        congr 1
        dsimp only [η]
        ring

end PolycyclicRecognition

end OAI
