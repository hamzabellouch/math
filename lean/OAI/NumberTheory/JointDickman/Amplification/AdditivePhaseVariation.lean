import OAI.NumberTheory.JointDickman.Amplification.PolylogMultiplicativeSum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace OAI

/-! # Finite partial summation for a nearby additive frequency -/
namespace JointDickman
open Finset

lemma additivePhase_sub_one_norm_le (t : ℝ) :
    ‖additivePhase t-1‖ ≤ 2*Real.pi*|t| := by
  have he : additivePhase t = Complex.exp (Complex.I*((2*Real.pi*t:ℝ):ℂ)) := by
    unfold additivePhase
    congr 1
    push_cast
    ring
  rw [he]
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2*Real.pi*t)
  simpa [Real.norm_eq_abs,abs_mul,abs_of_pos Real.pi_pos] using h

lemma additivePhase_difference_norm_le (x y : ℝ) :
    ‖additivePhase x-additivePhase y‖ ≤ 2*Real.pi*|x-y| := by
  have he : additivePhase x = additivePhase y*additivePhase (x-y) := by
    rw [←additivePhase_add]
    congr 1
    ring
  rw [he,show additivePhase y*additivePhase (x-y)-additivePhase y =
    additivePhase y*(additivePhase (x-y)-1) by ring,norm_mul,norm_additivePhase,one_mul]
  exact additivePhase_sub_one_norm_le (x-y)

lemma bounded_partial_sums_weighted (z w : ℕ → ℂ) (N : ℕ) (T M L : ℝ)
    (hT : 0 ≤ T) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hz : ∀ k ≤ N, ‖∑ i ∈ range k, z i‖ ≤ T)
    (hw : ∀ i < N, ‖w i‖ ≤ M)
    (hd : ∀ i < N, ‖w (i+1)-w i‖ ≤ L) :
    ‖∑ i ∈ range N, w i*z i‖ ≤ T*(M+N*L) := by
  cases N with
  | zero => simpa using mul_nonneg hT hM
  | succ N =>
    rw [show (∑ i ∈ range (N+1), w i*z i) = ∑ i ∈ range (N+1), w i • z i by simp]
    rw [sum_range_by_parts]
    simp only [Nat.add_sub_cancel,smul_eq_mul]
    have hf : ‖w N*(∑ i ∈ range (N+1), z i)‖ ≤ M*T := by
      rw [norm_mul]
      exact mul_le_mul (hw N (by omega)) (hz (N+1) le_rfl) (norm_nonneg _) hM
    have hs : ‖∑ i ∈ range N, (w (i+1)-w i)*(∑ j ∈ range (i+1), z j)‖ ≤ (N:ℝ)*(L*T) := by
      apply (norm_sum_le _ _).trans
      calc
        _ ≤ ∑ _i ∈ range N, L*T := by
          apply sum_le_sum
          intro i hi
          rw [norm_mul]
          exact mul_le_mul (hd i (by have := mem_range.mp hi; omega))
            (hz (i+1) (by have := mem_range.mp hi; omega)) (norm_nonneg _) hL
        _ = _ := by simp
    have hh := (norm_sub_le _ _).trans (add_le_add hf hs)
    apply hh.trans
    push_cast
    nlinarith

end JointDickman

end OAI
