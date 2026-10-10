import Mathlib.Analysis.Complex.Norm
import OAI.NumberTheory.Ostmann.QuadraticSieve.OddJacobiMoment

namespace OAI

/-! # The odd-modulus moment estimate for complex coefficient arrays -/

namespace Ostmann

open scoped BigOperators

theorem complex_odd_jacobi_even_moment_bound (hB : PublishedBonamiBound)
    (P S : Finset ℕ) (hS : ∀ s ∈ S, Squarefree s)
    (hP : ∀ s ∈ S, s.primeFactors ⊆ P) (U M l : ℕ)
    (hU : ∀ s ∈ S, s ≤ U) (hl : 0 < l) (b : S → ℂ) :
    (∑ m ∈ Finset.range M, if Odd m then
        ‖∑ s : S, b s * (realJacobi s.val m : ℂ)‖ ^ (2 * l) else 0) ≤
      (2 : ℝ) ^ (2 * l) * ((M : ℝ) *
        (∑ s : S, ((2 * l - 1 : ℕ) : ℝ) ^ s.val.primeFactors.card * ‖b s‖ ^ 2) ^ l +
      (8 * (U : ℝ) ^ (2 * l)) * (∑ s : S, ‖b s‖) ^ (2 * l)) := by
  classical
  let B := (M : ℝ) *
    (∑ s : S, ((2 * l - 1 : ℕ) : ℝ) ^ s.val.primeFactors.card * ‖b s‖ ^ 2) ^ l +
    (8 * (U : ℝ) ^ (2 * l)) * (∑ s : S, ‖b s‖) ^ (2 * l)
  have hcomponent (a : S → ℝ) (ha : ∀ s, |a s| ≤ ‖b s‖) :
      (∑ m ∈ Finset.range M, if Odd m then
        |∑ s : S, a s * realJacobi s.val m| ^ (2 * l) else 0) ≤ B := by
    apply (odd_jacobi_even_moment_bound hB P S hS hP U M l hU hl a).trans
    have he : (∑ s : S, ((2 * l - 1 : ℕ) : ℝ) ^ s.val.primeFactors.card * |a s| ^ 2) ≤
        ∑ s : S, ((2 * l - 1 : ℕ) : ℝ) ^ s.val.primeFactors.card * ‖b s‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro s hs
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (ha s) 2) (by positivity)
    have he0 : 0 ≤ ∑ s : S, ((2 * l - 1 : ℕ) : ℝ) ^ s.val.primeFactors.card * |a s| ^ 2 := by
      positivity
    have hsum : (∑ s : S, |a s|) ≤ ∑ s : S, ‖b s‖ := Finset.sum_le_sum (fun s _ => ha s)
    dsimp [B]
    exact add_le_add
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ he0 he l) (by positivity))
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hsum (2 * l)) (by positivity))
  have hre := hcomponent (fun s => (b s).re) (fun s => Complex.abs_re_le_norm (b s))
  have him := hcomponent (fun s => (b s).im) (fun s => Complex.abs_im_le_norm (b s))
  have hpoint (m : ℕ) :
      ‖∑ s : S, b s * (realJacobi s.val m : ℂ)‖ ^ (2 * l) ≤
        (2 : ℝ) ^ (2 * l - 1) *
          (|∑ s : S, (b s).re * realJacobi s.val m| ^ (2 * l) +
            |∑ s : S, (b s).im * realJacobi s.val m| ^ (2 * l)) := by
    let z := ∑ s : S, b s * (realJacobi s.val m : ℂ)
    have hz := (pow_le_pow_left₀ (norm_nonneg z) (Complex.norm_le_abs_re_add_abs_im z) (2 * l)).trans
      (add_pow_le (abs_nonneg z.re) (abs_nonneg z.im) (2 * l))
    simpa [z, Complex.mul_re, Complex.mul_im] using hz
  calc
    _ ≤ (2 : ℝ) ^ (2 * l - 1) *
        ((∑ m ∈ Finset.range M, if Odd m then
            |∑ s : S, (b s).re * realJacobi s.val m| ^ (2 * l) else 0) +
          ∑ m ∈ Finset.range M, if Odd m then
            |∑ s : S, (b s).im * realJacobi s.val m| ^ (2 * l) else 0) := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro m hm
      split_ifs with h
      · exact hpoint m
      · simp
    _ ≤ (2 : ℝ) ^ (2 * l - 1) * (B + B) :=
      mul_le_mul_of_nonneg_left (add_le_add hre him) (by positivity)
    _ = (2 : ℝ) ^ (2 * l) * B := by
      calc
        _ = ((2 : ℝ) ^ (2 * l - 1) * 2) * B := by ring
        _ = _ := by rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ 2 * l)]

end Ostmann

end OAI
