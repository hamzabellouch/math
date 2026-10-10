import OAI.NumberTheory.TwoPointCorrelations.MRTMeanSquare
import OAI.NumberTheory.JointDickman.Analysis.MellinAngularEnergy

namespace OAI

/-! # Finite duality for sampled Mellin polynomials

Finite duality reduces sparse-prime sampling to a row bound for the
weighted Mellin kernel.
-/
namespace JointDickman
open Finset TwoPointCorrelations
open scoped ComplexConjugate

lemma norm_finite_complex_pairing_sq {ι : Type*} (S : Finset ι) (a b : ι → ℂ) :
    ‖∑ n ∈ S, a n*b n‖^2 ≤
      (∑ n ∈ S, ‖a n‖^2)*(∑ n ∈ S, ‖b n‖^2) := by
  have h := norm_sum_le S (fun n => a n*b n)
  simp only [norm_mul] at h
  exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans
    (sum_mul_sq_le_sq_mul_sq S (fun n => ‖a n‖) (fun n => ‖b n‖))

/-- Finite transpose duality, with no compactness or limiting argument. -/
theorem mellin_samples_of_dual (P : Finset ℕ) (S : Finset ℝ)
    (a : ℕ → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hdual : ∀ b : ℝ → ℂ,
      (∑ n ∈ P, ‖∑ t ∈ S, b t *
        Complex.exp (((-Real.log (n : ℝ)*t : ℝ) : ℂ)*Complex.I)‖^2) ≤
          C*∑ t ∈ S, ‖b t‖^2) :
    (∑ t ∈ S, ‖mrtExponentialPolynomial P a (fun n => -Real.log (n : ℝ)) t‖^2) ≤
      C*∑ n ∈ P, ‖a n‖^2 := by
  let q := mrtExponentialPolynomial P a (fun n => -Real.log (n : ℝ))
  let d : ℕ → ℂ := fun n => ∑ t ∈ S, conj (q t)*
    Complex.exp (((-Real.log (n : ℝ)*t : ℝ) : ℂ)*Complex.I)
  let E : ℝ := ∑ t ∈ S, ‖q t‖^2
  let F : ℝ := ∑ n ∈ P, ‖a n‖^2
  have hE : 0 ≤ E := sum_nonneg fun _ _ => sq_nonneg _
  have hF : 0 ≤ F := sum_nonneg fun _ _ => sq_nonneg _
  have hpair : (∑ n ∈ P, a n*d n) = (E : ℂ) := by
    dsimp only [d, E]
    simp only [mul_sum, Complex.ofReal_sum, Complex.ofReal_pow, ← Complex.mul_conj']
    rw [sum_comm]
    apply sum_congr rfl
    intro t _
    dsimp only [q, mrtExponentialPolynomial]
    rw [sum_mul]
    apply sum_congr rfl
    intro n _
    ring
  have hD : (∑ n ∈ P, ‖d n‖^2) ≤ C*E := by
    simpa only [d, E, Complex.norm_conj] using hdual (fun t => conj (q t))
  have hsq := norm_finite_complex_pairing_sq P a d
  rw [hpair, Complex.norm_real, Real.norm_eq_abs, sq_abs] at hsq
  change E^2 ≤ F*∑ n ∈ P, ‖d n‖^2 at hsq
  have hh := hsq.trans (mul_le_mul_of_nonneg_left hD hF)
  change E ≤ C*F
  by_cases hz : E = 0
  · rw [hz]
    positivity
  · have hp : 0 < E := lt_of_le_of_ne hE (Ne.symm hz)
    nlinarith

noncomputable def mellinSampleKernel (P : Finset ℕ) (w : ℕ → ℝ) (t : ℝ) : ℂ :=
  ∑ n ∈ P, (w n : ℂ)*Complex.exp (((-Real.log (n : ℝ)*t : ℝ) : ℂ)*Complex.I)

lemma mellinSampleKernel_neg (P : Finset ℕ) (w : ℕ → ℝ) (t : ℝ) :
    mellinSampleKernel P w (-t) = conj (mellinSampleKernel P w t) := by
  unfold mellinSampleKernel
  simp only [map_sum, map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  apply sum_congr rfl
  intro n _
  congr 2
  simp only [Complex.conj_I, Complex.ofReal_mul, Complex.ofReal_neg]
  ring

lemma mellin_weighted_dual_identity (P : Finset ℕ) (S : Finset ℝ)
    (w : ℕ → ℝ) (b : ℝ → ℂ) :
    (∑ n ∈ P, w n*‖∑ t ∈ S, b t *
      Complex.exp (((-Real.log (n : ℝ)*t : ℝ) : ℂ)*Complex.I)‖^2) =
      ∑ t ∈ S, ∑ u ∈ S,
        ((b t*conj (b u))*mellinSampleKernel P w (t-u)).re := by
  have he : ((∑ n ∈ P, w n*‖∑ t ∈ S, b t *
      Complex.exp (((-Real.log (n : ℝ)*t : ℝ) : ℂ)*Complex.I)‖^2 : ℝ) : ℂ) =
      ∑ t ∈ S, ∑ u ∈ S,
        (b t*conj (b u))*mellinSampleKernel P w (t-u) := by
    simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow,
      ← Complex.mul_conj', map_sum, map_mul, sum_mul, mul_sum]
    rw [sum_comm]
    conv_lhs => arg 2; ext t; rw [sum_comm]
    rw [sum_comm (s := S) (t := S)]
    apply sum_congr rfl
    intro t _
    apply sum_congr rfl
    intro u _
    unfold mellinSampleKernel
    rw [mul_sum]
    apply sum_congr rfl
    intro n _
    have hh := mrt_phase_pair (-Real.log (n : ℝ)*t) (-Real.log (n : ℝ)*u)
    rw [show -Real.log (n : ℝ)*t - -Real.log (n : ℝ)*u =
      -Real.log (n : ℝ)*(t-u) by ring] at hh
    rw [← hh]
    simp only [Complex.ofReal_mul, Complex.ofReal_neg, mul_assoc, mul_comm, mul_left_comm]
  simpa only [Complex.ofReal_re, Complex.re_sum] using congrArg Complex.re he

/-- A row bound for the weighted Mellin kernel controls the dual
quadratic form. -/
theorem mellin_weighted_dual_rows (P : Finset ℕ) (S : Finset ℝ)
    (w : ℕ → ℝ) {C : ℝ}
    (hrow : ∀ t ∈ S, ∑ u ∈ S, ‖mellinSampleKernel P w (t-u)‖ ≤ C)
    (b : ℝ → ℂ) :
    (∑ n ∈ P, w n*‖∑ t ∈ S, b t *
      Complex.exp (((-Real.log (n : ℝ)*t : ℝ) : ℂ)*Complex.I)‖^2) ≤
        C*∑ t ∈ S, ‖b t‖^2 := by
  rw [mellin_weighted_dual_identity]
  apply le_trans (b := ∑ t ∈ S, ∑ u ∈ S,
    ‖b t‖*‖b u‖*‖mellinSampleKernel P w (t-u)‖)
  · apply sum_le_sum
    intro t _
    apply sum_le_sum
    intro u _
    simpa only [norm_mul, Complex.norm_conj] using Complex.re_le_norm
      ((b t*conj (b u))*mellinSampleKernel P w (t-u))
  · apply mrt_symmetric_row_bound S _ (fun t => ‖b t‖) C
      (fun _ _ _ _ => norm_nonneg _) _ hrow
    intro t _ u _
    have hh := mellinSampleKernel_neg P w (t-u)
    rw [neg_sub] at hh
    rw [hh, Complex.norm_conj]

end JointDickman

end OAI
