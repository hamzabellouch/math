import OAI.Algebra.DepthFive.ImmFirstTrace
import OAI.Algebra.DepthFive.PathMassParameters

namespace OAI

noncomputable section
open scoped BigOperators Matrix

namespace Problem335

open LowerParameters

/-- The first trace of the actual finite normalized IMM matrix at the canonical
occupation parameters. The path-count and geometric scale agree with the second
moment normalization; there are no auxiliary matrix-identity hypotheses. -/
theorem immNormalizedMatrix_first_moment_lower_parameters {n : ℕ} (hn : 16 ≤ n)
    (side : Fin n → Bool) (hk : immLayerVCount side = k n)
    (hm : immLayerUCount side = m n) :
    (Fintype.card (ImmSourceIndex n side (a n) (b n)) : ℝ) *
      ((n : ℝ) ^ (n - 1) *
        (((a n : ℝ) / v n) ^ k n * (1 + (b n : ℝ) / u n) ^ m n)) *
          Real.exp (-64 / Real.sqrt (n : ℝ)) ≤
      ((immNormalizedMatrix n side (a n) (b n)).conjTranspose *
        immNormalizedMatrix n side (a n) (b n)).trace.re := by
  classical
  have h := immNormalizedMatrix_first_trace_lower_of_average n (by omega)
    side (a n) (b n)
    (Real.exp (-64 / Real.sqrt (n : ℝ)) *
      (((a n : ℝ) / v n) ^ k n * (1 + (b n : ℝ) / u n) ^ m n)) (by
      intro p
      have hpath := immPath_source_mass_lower_parameters hn side hk hm
        ((immPaths n (by omega)).get p) (List.get_mem _ p)
      change _ ≤ (∑ d : ImmSourceIndex n side (a n) (b n),
        immPathAmplitude n (by omega) (fun x => side x.1) d.1 p ^ 2) /
          (Fintype.card (ImmSourceIndex n side (a n) (b n)) : ℝ) at hpath
      exact hpath)
  simpa only [mul_assoc, mul_left_comm, mul_comm] using h

/-- A weaker square-root-exponential version is convenient for the final
rank lower bound, whose constant absorbs both trace losses. -/
theorem immNormalizedMatrix_first_moment_lower_sqrt {n : ℕ} (hn : 16 ≤ n)
    (side : Fin n → Bool) (hk : immLayerVCount side = k n)
    (hm : immLayerUCount side = m n) :
    (Fintype.card (ImmSourceIndex n side (a n) (b n)) : ℝ) *
      ((n : ℝ) ^ (n - 1) *
        (((a n : ℝ) / v n) ^ k n * (1 + (b n : ℝ) / u n) ^ m n)) *
          Real.exp (-64 * Real.sqrt (n : ℝ)) ≤
      ((immNormalizedMatrix n side (a n) (b n)).conjTranspose *
        immNormalizedMatrix n side (a n) (b n)).trace.re := by
  have hs := sqrt_ge_four hn
  have hspos : 0 < Real.sqrt (n : ℝ) := by linarith
  have hexp : Real.exp (-64 * Real.sqrt (n : ℝ)) ≤
      Real.exp (-64 / Real.sqrt (n : ℝ)) := by
    apply Real.exp_le_exp.mpr
    apply (le_div_iff₀ hspos).mpr
    nlinarith [sq_nonneg (Real.sqrt (n : ℝ) - 1)]
  exact (mul_le_mul_of_nonneg_left hexp (by positivity)).trans
    (immNormalizedMatrix_first_moment_lower_parameters hn side hk hm)

end Problem335

end

end OAI
