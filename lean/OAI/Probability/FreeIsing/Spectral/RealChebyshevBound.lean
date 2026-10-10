import Mathlib

namespace OAI

open Polynomial
namespace Problem367

lemma chebyshev_pell (n : ℕ) :
    Chebyshev.T ℝ ((n : ℤ) + 1) ^ 2 +
      (1 - (X : ℝ[X]) ^ 2) * Chebyshev.U ℝ (n : ℤ) ^ 2 = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Nat.cast_succ]
    rw [show (n : ℤ) + 1 + 1 = (n : ℤ) + 2 by ring,
      Chebyshev.T_eq_X_mul_T_sub_pol_U, Chebyshev.U_eq_X_mul_U_add_T]
    calc
      _ = Chebyshev.T ℝ ((n : ℤ) + 1) ^ 2 +
          (1 - (X : ℝ[X]) ^ 2) * Chebyshev.U ℝ (n : ℤ) ^ 2 := by ring
      _ = 1 := ih
end Problem367
namespace Problem367
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma isSelfAdjoint_aeval_real (B : E →L[ℝ] E) (hB : IsSelfAdjoint B) (p : ℝ[X]) :
    IsSelfAdjoint (aeval B p) := by
  induction p using Polynomial.induction_on with
  | C r =>
    simpa using (show IsSelfAdjoint r from rfl).algebraMap (E →L[ℝ] E)
  | add p q hp hq => simpa using hp.add hq
  | monomial n r ih =>
    simp only [map_mul, map_pow, aeval_C, aeval_X]
    rw [← Algebra.smul_def]
    exact (show IsSelfAdjoint r from rfl).smul (hB.pow _)

omit [CompleteSpace E] in
lemma commute_aeval_self (B : E →L[ℝ] E) (p : ℝ[X]) : Commute B (aeval B p) := by
  simpa using (Commute.all (X : ℝ[X]) p).map (aeval B)
end
end Problem367
namespace Problem367
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma selfAdjoint_inner_square (P : E →L[ℝ] E) (hP : IsSelfAdjoint P) (x : E) :
    inner ℝ x ((P ^ 2) x) = ‖P x‖ ^ 2 := by
  rw [pow_two, mul_apply_eq_comp]
  exact ((hP.isSymmetric x (P x)).symm).trans (real_inner_self_eq_norm_sq _)

lemma norm_le_one_of_pell (B P Q : E →L[ℝ] E)
    (hB : IsSelfAdjoint B) (hP : IsSelfAdjoint P) (hQ : IsSelfAdjoint Q)
    (hBQ : Commute B Q) (hBnorm : ‖B‖ ≤ 1)
    (hidentity : P ^ 2 + (1 - B ^ 2) * Q ^ 2 = 1) : ‖P‖ ≤ 1 := by
  have hBQsa : IsSelfAdjoint (B * Q) := (hB.commute_iff hQ).mp hBQ
  have hid : P ^ 2 + Q ^ 2 - (B * Q) ^ 2 = 1 := by
    rw [hBQ.mul_pow]
    calc
      P ^ 2 + Q ^ 2 - B ^ 2 * Q ^ 2 = P ^ 2 + (1 - B ^ 2) * Q ^ 2 := by noncomm_ring
      _ = 1 := hidentity
  refine P.opNorm_le_bound (by norm_num) fun x => ?_
  have heq := congrArg (fun A : E →L[ℝ] E => inner ℝ x (A x)) hid
  simp only [sub_apply, add_apply,
    one_apply_eq_self, inner_sub_right, inner_add_right,
    selfAdjoint_inner_square P hP x, selfAdjoint_inner_square Q hQ x,
    selfAdjoint_inner_square (B * Q) hBQsa x, real_inner_self_eq_norm_sq,
    mul_apply_eq_comp] at heq
  have hb : ‖B (Q x)‖ ≤ ‖Q x‖ := by
    calc
      ‖B (Q x)‖ ≤ ‖B‖ * ‖Q x‖ := B.le_opNorm _
      _ ≤ 1 * ‖Q x‖ := mul_le_mul_of_nonneg_right hBnorm (norm_nonneg _)
      _ = ‖Q x‖ := one_mul _
  have hb2 : ‖B (Q x)‖ ^ 2 ≤ ‖Q x‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hb 2
  simp only [one_mul]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  linarith

end
end Problem367
namespace Problem367
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma norm_aeval_chebyshev_T_le_real (B : E →L[ℝ] E)
    (hB : IsSelfAdjoint B) (hBnorm : ‖B‖ ≤ 1) (n : ℕ) :
    ‖aeval B (Chebyshev.T ℝ (n : ℤ))‖ ≤ 1 := by
  cases n with
  | zero =>
    simp only [Nat.cast_zero, Chebyshev.T_zero, map_one]
    exact ContinuousLinearMap.norm_id_le
  | succ n =>
    simp only [Nat.cast_succ]
    apply norm_le_one_of_pell B _ (aeval B (Chebyshev.U ℝ (n : ℤ))) hB
      (isSelfAdjoint_aeval_real B hB _) (isSelfAdjoint_aeval_real B hB _)
      (commute_aeval_self B _) hBnorm
    have h := congrArg (aeval B) (chebyshev_pell n)
    simpa only [map_add, map_mul, map_sub, map_pow, map_one, aeval_X] using h

lemma norm_aeval_chebyshev_U_le_real (B : E →L[ℝ] E)
    (hB : IsSelfAdjoint B) (hBnorm : ‖B‖ ≤ 1) (n : ℕ) :
    ‖aeval B (Chebyshev.U ℝ (n : ℤ))‖ ≤ (n : ℝ) + 1 := by
  induction n using Nat.twoStepInduction with
  | zero =>
    simp only [Nat.cast_zero, Chebyshev.U_zero, map_one, zero_add]
    exact ContinuousLinearMap.norm_id_le
  | one =>
    simpa [Chebyshev.U_one, map_ofNat, two_mul] using
      (norm_add_le B B).trans (add_le_add hBnorm hBnorm)
  | more n ih0 ih1 =>
    simp only [Nat.cast_add, Nat.cast_ofNat, Chebyshev.U_eq_two_mul_T_add_U,
      map_add, two_mul]
    have hT := norm_aeval_chebyshev_T_le_real B hB hBnorm (n + 2)
    simp only [Nat.cast_add, Nat.cast_ofNat] at hT
    calc
      _ ≤ (‖aeval B (Chebyshev.T ℝ ((n : ℤ) + 2))‖ +
          ‖aeval B (Chebyshev.T ℝ ((n : ℤ) + 2))‖) +
          ‖aeval B (Chebyshev.U ℝ (n : ℤ))‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ (n : ℝ) + 2 + 1 := by linarith
end
end Problem367

end OAI
