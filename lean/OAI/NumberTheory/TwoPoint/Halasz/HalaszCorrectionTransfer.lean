import OAI.NumberTheory.TwoPoint.Halasz.HalaszHyperbolaRows
import OAI.NumberTheory.TwoPoint.Halasz.HalaszPrimePowers
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCorrectionSummability

namespace OAI

/-! Transfer an ordinary mean estimate through the exact prime-power
correction, retaining its uniform summable tail. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma halasz_correction_prefix (f : ℕ → ℂ) (hf : Multiplicative f) (hf1 : f 1 = 1)
    (N : ℕ) :
    (∑ n ∈ Icc 1 N, f n) =
      ∑ d ∈ Icc 1 N, mrtCorrection f d * ∑ n ∈ Icc 1 (N / d), mrtCompletePart f n := by
  calc
    _ = ∑ n ∈ Icc 1 N, ∑ p ∈ n.divisorsAntidiagonal,
        mrtCorrection f p.1 * mrtCompletePart f p.2 := by
      apply sum_congr rfl
      intro n hn
      rw [Nat.sum_divisorsAntidiagonal (fun d m => mrtCorrection f d * mrtCompletePart f m)]
      exact mrt_multiplicative_divisor_sum f hf hf1 (mem_Icc.mp hn).1
    _ = _ := by
      rw [halasz_sum_divisorsAntidiagonal (fun d n => mrtCorrection f d * mrtCompletePart f n),
        halasz_hyperbola_rows (fun d n => mrtCorrection f d * mrtCompletePart f n)]
      exact sum_congr rfl (fun d _ => (mul_sum _ _ _).symm)

theorem halasz_correction_mean_bound (f : ℕ → ℂ) (hf : Multiplicative f)
    (hbound : OneBounded f) (hf1 : f 1 = 1) (N W : ℕ) (hW : 0 < W)
    (A : ℝ) (hA : 0 ≤ A)
    (hmean : ∀ d ∈ Icc 1 N, d ≤ W →
      ‖∑ n ∈ Icc 1 (N / d), mrtCompletePart f n‖ ≤ A * ((N / d : ℕ) : ℝ)) :
    ‖∑ n ∈ Icc 1 N, f n‖ ≤
      mrtCorrectionBound * N * (A + (W : ℝ) ^ (-(1 / 4 : ℝ))) := by
  let S := (Icc 1 N).filter (fun d => d ≤ W)
  let U := (Icc 1 N).filter (fun d => ¬d ≤ W)
  let a := fun d : ℕ => mrtCorrection f d * ∑ n ∈ Icc 1 (N / d), mrtCompletePart f n
  have hsplit : (∑ n ∈ Icc 1 N, f n) = (∑ d ∈ S, a d) + ∑ d ∈ U, a d := by
    rw [halasz_correction_prefix f hf hf1]
    exact (sum_filter_add_sum_filter_not (Icc 1 N) (fun d => d ≤ W) a).symm
  have hs : ‖∑ d ∈ S, a d‖ ≤ (A * N) * ∑ d ∈ S, ‖mrtCorrection f d‖ / (d : ℝ) := by
    apply (norm_sum_le _ _).trans
    rw [mul_sum]
    apply sum_le_sum
    intro d hd
    obtain ⟨hdN, hdW⟩ := mem_filter.mp hd
    rw [show a d = mrtCorrection f d * ∑ n ∈ Icc 1 (N / d), mrtCompletePart f n from rfl, norm_mul]
    calc
      _ ≤ ‖mrtCorrection f d‖ * (A * ((N / d : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left (hmean d hdN hdW) (norm_nonneg _)
      _ ≤ ‖mrtCorrection f d‖ * (A * ((N : ℝ) / d)) := by
        gcongr
        exact Nat.cast_div_le
      _ = _ := by ring
  have hu : ‖∑ d ∈ U, a d‖ ≤ (N : ℝ) * ∑ d ∈ U, ‖mrtCorrection f d‖ / (d : ℝ) := by
    apply (norm_sum_le _ _).trans
    rw [mul_sum]
    apply sum_le_sum
    intro d hd
    rw [show a d = mrtCorrection f d * ∑ n ∈ Icc 1 (N / d), mrtCompletePart f n from rfl, norm_mul]
    calc
      _ ≤ ‖mrtCorrection f d‖ * ((N / d : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left
          (halasz_bounded_prefix_norm _ (mrtCompletePart_oneBounded f hbound) _) (norm_nonneg _)
      _ ≤ ‖mrtCorrection f d‖ * ((N : ℝ) / d) :=
        mul_le_mul_of_nonneg_left Nat.cast_div_le (norm_nonneg _)
      _ = _ := by ring
  have hsmass : (∑ d ∈ S, ‖mrtCorrection f d‖ / (d : ℝ)) ≤ mrtCorrectionBound := by
    simpa using mrt_correction_tail_bound f hbound hf1 (W := 1) (by norm_num) S
      (fun d hd => (mem_Icc.mp (mem_filter.mp hd).1).1)
  have humass := mrt_correction_tail_bound f hbound hf1 hW U
    (fun d hd => Nat.le_of_lt (Nat.lt_of_not_ge (mem_filter.mp hd).2))
  calc
    _ ≤ ‖∑ d ∈ S, a d‖ + ‖∑ d ∈ U, a d‖ := by rw [hsplit]; exact norm_add_le _ _
    _ ≤ (A * N) * (∑ d ∈ S, ‖mrtCorrection f d‖ / (d : ℝ)) +
        (N : ℝ) * (∑ d ∈ U, ‖mrtCorrection f d‖ / (d : ℝ)) := add_le_add hs hu
    _ ≤ (A * N) * mrtCorrectionBound +
        (N : ℝ) * (mrtCorrectionBound * (W : ℝ) ^ (-(1 / 4 : ℝ))) := by gcongr
    _ = _ := by ring

end TwoPointCorrelations

end OAI
