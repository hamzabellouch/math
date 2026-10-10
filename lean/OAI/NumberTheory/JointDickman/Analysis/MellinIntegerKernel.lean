import OAI.NumberTheory.JointDickman.Analysis.LogPhaseSharpBounds
import OAI.NumberTheory.JointDickman.Arithmetic.SeparatedHarmonicKernel

namespace OAI

/-! # The actual integer Mellin kernel on a dyadic interval -/
namespace JointDickman
open Finset Problem337 TwoPointCorrelations

lemma mellin_integer_kernel_phase (L R : ℕ) (t : ℝ) :
    mellinSampleKernel (Icc L R) (fun _ => 1) t =
      ∑ n ∈ Icc L R, ExponentialSum.phase ((-t/(2*Real.pi))*Real.log (n:ℝ)) := by
  unfold mellinSampleKernel ExponentialSum.phase
  apply sum_congr rfl
  intro n _
  simp only [Complex.ofReal_one, one_mul]
  congr 2
  push_cast
  field_simp

/-- A sharp dyadic Mellin kernel has reciprocal decay below its length,
and a square-root error beyond it. -/
theorem mellin_integer_kernel_bound {U : ℝ} (hU : 1 ≤ U) (L R : ℕ)
    (hL : U ≤ (L:ℝ)) (hR : (R:ℝ) ≤ 2*U) (t : ℝ) :
    ‖mellinSampleKernel (Icc L R) (fun _ => 1) t‖ ≤
      16000*(U/(1+|t|)+Real.sqrt |t|) := by
  have hp : 1 ≤ 2*Real.pi := by linarith [Real.pi_gt_three]
  have hp8 : 2*Real.pi ≤ 8 := by linarith [Real.pi_lt_four]
  have hp0 : 0 < 2*Real.pi := by positivity
  have habs : |-t/(2*Real.pi)| = |t|/(2*Real.pi) := by
    rw [abs_div, abs_neg, abs_of_pos hp0]
  have hd : U/(1+|t|/(2*Real.pi)) ≤ (2*Real.pi)*(U/(1+|t|)) := by
    rw [show (2*Real.pi)*(U/(1+|t|)) = ((2*Real.pi)*U)/(1+|t|) by ring]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have he : (2*Real.pi)*U*(1+|t|/(2*Real.pi)) = U*(2*Real.pi+|t|) := by field_simp
    rw [he]
    nlinarith
  have hs : Real.sqrt (|t|/(2*Real.pi)) ≤ Real.sqrt |t| := by
    apply Real.sqrt_le_sqrt
    exact div_le_self (abs_nonneg t) hp
  rw [mellin_integer_kernel_phase]
  have hh := log_phase_sharp_bound hU (-t/(2*Real.pi)) L R hL hR
  rw [habs] at hh
  apply hh.trans
  have hd0 : 0 ≤ U/(1+|t|) := by positivity
  have hsq0 := Real.sqrt_nonneg |t|
  nlinarith

/-- The concrete sharp integer kernel has a logarithmic row bound, plus
a cost proportional to the number of sampled frequencies. -/
theorem mellin_integer_kernel_rows {U : ℝ} (hU : 1 ≤ U) (L R : ℕ)
    (hL : U ≤ (L:ℝ)) (hR : (R:ℝ) ≤ 2*U)
    (S : Finset ℝ) (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x-y|)
    {T : ℝ} (hT : 0 ≤ T)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, |x-y| ≤ T) (t : ℝ) (ht : t ∈ S) :
    (∑ u ∈ S, ‖mellinSampleKernel (Icc L R) (fun _ => 1) (t-u)‖) ≤
      16000*(2*U*(1+Real.log (T+1))+(S.card:ℝ)*Real.sqrt T) := by
  calc
    _ ≤ ∑ u ∈ S, 16000*(U/(1+|t-u|)+Real.sqrt T) := by
      apply sum_le_sum
      intro u hu
      apply (mellin_integer_kernel_bound hU L R hL hR (t-u)).trans
      exact mul_le_mul_of_nonneg_left (add_le_add le_rfl
        (Real.sqrt_le_sqrt (hdiam t ht u hu))) (by norm_num)
    _ = 16000*(U*(∑ u ∈ S, 1/(1+|t-u|))+(S.card:ℝ)*Real.sqrt T) := by
      simp only [div_eq_mul_inv, mul_add, mul_sum, sum_add_distrib, sum_const, nsmul_eq_mul]
      ring_nf
    _ ≤ _ := by
      have hh := separated_harmonic_kernel_sum S hsep t T hT (hdiam t ht)
      nlinarith

end JointDickman

end OAI
