import OAI.NumberTheory.JointDickman.Analysis.MellinIntegerKernel

namespace OAI

/-! # Sparse sampling of the actual integer cofactor polynomial -/
namespace JointDickman
open Finset TwoPointCorrelations

/-- Finite duality for sharp integer intervals, with the square-root
frequency error charged only once per sampled point. -/
theorem sparse_integer_mellin_sampling {U : ℝ} (hU : 1 ≤ U) (L R : ℕ)
    (hL : U ≤ (L:ℝ)) (hR : (R:ℝ) ≤ 2*U)
    (S : Finset ℝ) (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x-y|)
    {T : ℝ} (hT : 0 ≤ T) (hdiam : ∀ x ∈ S, ∀ y ∈ S, |x-y| ≤ T)
    (a : ℕ → ℂ) :
    (∑ t ∈ S, ‖mrtExponentialPolynomial (Icc L R) a
      (fun n => -Real.log (n:ℝ)) t‖^2) ≤
      16000*(2*U*(1+Real.log (T+1))+(S.card:ℝ)*Real.sqrt T)*
        ∑ n ∈ Icc L R, ‖a n‖^2 := by
  have hlog : 0 ≤ Real.log (T+1) := Real.log_nonneg (by linarith)
  apply mellin_samples_of_dual _ S a (by positivity)
  intro b
  simpa only [one_mul] using mellin_weighted_dual_rows (Icc L R) S (fun _ => 1)
    (mellin_integer_kernel_rows hU L R hL hR S hsep hT hdiam) b

lemma reciprocal_cofactor_mass {U : ℝ} (hU : 1 ≤ U) (L R : ℕ)
    (hL : U ≤ (L:ℝ)) (hR : (R:ℝ) ≤ 2*U)
    (a : ℕ → ℂ) (ha : ∀ n ∈ Icc L R, ‖a n‖ ≤ 1/(n:ℝ)) :
    (∑ n ∈ Icc L R, ‖a n‖^2) ≤ 3/U := by
  have hU0 : 0 < U := by linarith
  have hm : (∑ n ∈ Icc L R, ‖a n‖^2) ≤ ((Icc L R).card:ℝ)/U^2 := by
    calc
      _ ≤ ∑ _n ∈ Icc L R, (1/U)^2 := by
        apply sum_le_sum
        intro n hn
        have hnU : U ≤ (n:ℝ) := hL.trans (by exact_mod_cast (mem_Icc.mp hn).1)
        apply pow_le_pow_left₀ (norm_nonneg _)
        exact (ha n hn).trans (one_div_le_one_div_of_le hU0 hnU)
      _ = _ := by simp only [sum_const, nsmul_eq_mul]; ring
  have hc : ((Icc L R).card:ℝ) ≤ 3*U := by
    have hh : ((Icc L R).card:ℝ) ≤ (R:ℝ)+1 := by
      exact_mod_cast (show (Icc L R).card ≤ R+1 by rw [Nat.card_Icc]; omega)
    linarith
  calc
    _ ≤ ((Icc L R).card:ℝ)/U^2 := hm
    _ ≤ 3*U/U^2 := div_le_div_of_nonneg_right hc (sq_nonneg _)
    _ = _ := by field_simp

/-- The normalized cofactor estimate required in the small-prime class of
the exceptional-frequency decomposition. Coefficients may already include
finite-prime masks and the reciprocal prime-count weight. -/
theorem sparse_reciprocal_cofactor_sampling {U : ℝ} (hU : 1 ≤ U) (L R : ℕ)
    (hL : U ≤ (L:ℝ)) (hR : (R:ℝ) ≤ 2*U)
    (S : Finset ℝ) (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x-y|)
    {T : ℝ} (hT : 0 ≤ T) (hdiam : ∀ x ∈ S, ∀ y ∈ S, |x-y| ≤ T)
    (a : ℕ → ℂ) (ha : ∀ n ∈ Icc L R, ‖a n‖ ≤ 1/(n:ℝ)) :
    (∑ t ∈ S, ‖mrtExponentialPolynomial (Icc L R) a
      (fun n => -Real.log (n:ℝ)) t‖^2) ≤
      48000*(2*(1+Real.log (T+1))+(S.card:ℝ)*Real.sqrt T/U) := by
  have hlog : 0 ≤ Real.log (T+1) := Real.log_nonneg (by linarith)
  have hh := sparse_integer_mellin_sampling hU L R hL hR S hsep hT hdiam a
  apply hh.trans
  calc
    _ ≤ 16000*(2*U*(1+Real.log (T+1))+(S.card:ℝ)*Real.sqrt T)*(3/U) :=
      mul_le_mul_of_nonneg_left (reciprocal_cofactor_mass hU L R hL hR a ha) (by positivity)
    _ = _ := by field_simp; ring

end JointDickman

end OAI
