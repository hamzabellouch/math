import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialEnvelopes
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SequenceVolumeComparison
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequenceSubexponentialOperations

namespace OAI

/-! # Vanishing thickening error for the constructed support paths -/

namespace PolycyclicRecognition

open Filter
open scoped Topology

/-- Linear path speed and logarithmic additive error have the precise
subexponential bounds required by the path-lifting construction. The
profile and short-switch errors fit one explicitly vanishing tolerance. -/
theorem exists_controlled_path_error_envelope
    (scale η : ℕ → ℝ) (hs : Tendsto scale atTop atTop) (hs1 : ∀ n, 1 ≤ scale n)
    (hη0 : ∀ n, 0 ≤ η n) (hη : Tendsto η atTop (𝓝 0))
    (A B K : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hK : 0 ≤ K) :
    ∃ ε : ℕ → ℝ, (∀ n, 0 ≤ ε n) ∧ Tendsto ε atTop (𝓝 0) ∧
      HasSubexponentialUpperBoundSeq scale (fun n => A * scale n) ∧
      HasSubexponentialUpperBoundSeq scale (fun n => B * (1 + Real.log (2 + scale n))) ∧
      ∀ n, K * (B * (1 + Real.log (2 + scale n)) + 2) +
        (2 * scale n * η n + A * (1 + Real.log (2 + scale n))) ≤ scale n * ε n := by
  let ε := fun n => 2 * η n +
    (K * B + A) * ((1 + Real.log (2 + scale n)) / scale n) + 2 * K / scale n
  have hs0 (n) : 0 < scale n := lt_of_lt_of_le zero_lt_one (hs1 n)
  have hlog (n) : 0 ≤ Real.log (2 + scale n) := Real.log_nonneg (by linarith [hs1 n])
  have hinv : Tendsto (fun n => 1 / scale n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hs
  have hloglim : Tendsto (fun n => Real.log (2 + scale n) / scale n) atTop (𝓝 0) :=
    log_shift_div_tendsto_zero.comp hs
  have hlim : Tendsto ε atTop (𝓝 0) := by
    have hh := ((hη.const_mul 2).add
      ((hinv.add hloglim).const_mul (K * B + A))).add
        (tendsto_const_nhds.div_atTop hs : Tendsto (fun n => 2 * K / scale n) atTop (𝓝 0))
    simpa only [ε, add_div, mul_zero, add_zero] using hh
  have hspeed : HasSubexponentialUpperBoundSeq scale (fun n => A * scale n) := by
    have hp := (subexponential_upper_polynomial (by linarith : 0 < A + 1) 1).along_sequence hs
    intro δ hδ
    filter_upwards [hp δ hδ] with n hn
    apply le_trans _ hn
    dsimp only [Function.comp_def]
    rw [pow_one]
    nlinarith [hs1 n]
  have hadditive : HasSubexponentialUpperBoundSeq scale
      (fun n => B * (1 + Real.log (2 + scale n))) := by
    have hp := (subexponential_upper_polynomial (by linarith : 0 < B + 1) 2).along_sequence hs
    intro δ hδ
    filter_upwards [hp δ hδ] with n hn
    apply le_trans _ hn
    have hl := Real.log_le_sub_one_of_pos (show 0 < 2 + scale n by linarith [hs1 n])
    dsimp only [Function.comp_def]
    have hb : 1 + Real.log (2 + scale n) ≤ (1 + scale n) ^ 2 := by nlinarith [hs1 n]
    calc
      _ ≤ B * (1 + scale n) ^ 2 := mul_le_mul_of_nonneg_left hb hB
      _ ≤ (B + 1) * (1 + scale n) ^ 2 := by nlinarith [sq_nonneg (1 + scale n)]
  refine ⟨ε, fun n => ?_, hlim, hspeed, hadditive, ?_⟩
  · dsimp only [ε]
    have := hη0 n
    have := hlog n
    have := (hs0 n).le
    positivity
  · intro n
    have he : scale n * ε n = K * (B * (1 + Real.log (2 + scale n)) + 2) +
        (2 * scale n * η n + A * (1 + Real.log (2 + scale n))) := by
      dsimp only [ε]
      field_simp [(hs0 n).ne']
      ring
    exact he.ge

end PolycyclicRecognition

end OAI
