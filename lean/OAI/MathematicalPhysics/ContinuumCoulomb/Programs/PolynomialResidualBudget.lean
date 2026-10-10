import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.PolynomialConstantBounds
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.SlabPolynomialResidual

namespace OAI

/-! A fixed polynomial scale absorbs the four residual contributions after
physical amplification. The exponent can be chosen before the source size. -/

noncomputable section
namespace ContinuumCoulomb

theorem logarithmic_separation_residual {N D : ℝ} (hN : 2 ≤ N) (k : ℕ)
    (hD : 25*(k:ℝ)*Real.log N ≤ D) :
    Real.exp (-(19/10:ℝ)*D) ≤ ((N^k)^40)⁻¹ := by
  have hN0 : 0 < N := by linarith
  have hklog : 0 ≤ (k:ℝ)*Real.log N :=
    mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by linarith))
  have he := Real.exp_le_exp.mpr
    (show -(19/10:ℝ)*D ≤ -40*(k:ℝ)*Real.log N by nlinarith only [hD,hklog])
  apply he.trans_eq
  rw [show -40*(k:ℝ)*Real.log N = -((40*k:ℕ):ℝ)*Real.log N by push_cast; ring,
    neg_mul,Real.exp_neg,Real.exp_nat_mul,Real.exp_log hN0]
  congr 1
  rw [← pow_mul]
  congr 1
  omega

theorem exists_four_residual_power (A B C D : ℝ)
    (_hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (_hD : 0 ≤ D) (s p : ℕ) :
    ∃ k₀ : ℕ, 1 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k → ∀ N : ℝ, 2 ≤ N →
      A*N^s/(N^k)^10+B*N^s/(N^k)^40+C*N^s/(N^k)^30+D*N^s/(N^k)^10 ≤
        (N^p)⁻¹ := by
  obtain ⟨q,hq,hconst⟩ := exists_polynomial_constant_bounds
    (show (0:ℝ)<1 by norm_num) (A+B+C+D)
  refine ⟨q+s+p+1,by omega,fun k hk N hN => ?_⟩
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hR : 1 ≤ N^k := one_le_pow₀ hN1
  have hB' : B*N^s/(N^k)^40 ≤ B*N^s/(N^k)^10 :=
    div_le_div_of_nonneg_left (by positivity) (by positivity)
      (pow_le_pow_right₀ hR (by decide : 10 ≤ 40))
  have hC' : C*N^s/(N^k)^30 ≤ C*N^s/(N^k)^10 :=
    div_le_div_of_nonneg_left (by positivity) (by positivity)
      (pow_le_pow_right₀ hR (by decide : 10 ≤ 30))
  calc
    _ ≤ A*N^s/(N^k)^10+B*N^s/(N^k)^10+C*N^s/(N^k)^10+D*N^s/(N^k)^10 :=
      add_le_add (add_le_add (add_le_add le_rfl hB') hC') le_rfl
    _ = (A+B+C+D)*N^s/(N^k)^10 := by ring
    _ ≤ N^q*N^s/(N^k)^10 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right (hconst N hN).2 (by positivity)
    _ = N^(q+s)/N^(k*10) := by rw [pow_add,pow_mul]
    _ ≤ (N^p)⁻¹ := by
      rw [inv_eq_one_div,div_le_div_iff₀ (pow_pos hN0 _) (pow_pos hN0 _),
        one_mul,← pow_add]
      exact pow_le_pow_right₀ hN1 (by omega)

theorem exists_four_residual_norm_offset (A B C D : ℝ)
    (_hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (_hD : 0 ≤ D) :
    ∃ k₀ : ℕ, 1 ≤ k₀ ∧ ∀ s k : ℕ, k₀+s ≤ k → ∀ N : ℝ, 2 ≤ N →
      A*N^s/(N^k)^40+B*N^s/(N^k)^70+C*N^s/(N^k)^60+D*N^s/(N^k)^40 ≤
        ((N^k)^19)⁻¹^2 := by
  obtain ⟨q,hq,hconst⟩ := exists_polynomial_constant_bounds
    (show (0:ℝ)<1 by norm_num) (A+B+C+D)
  refine ⟨q+1,by omega,fun s k hk N hN => ?_⟩
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hR : 1 ≤ N^k := one_le_pow₀ hN1
  have hB' : B*N^s/(N^k)^70 ≤ B*N^s/(N^k)^40 :=
    div_le_div_of_nonneg_left (by positivity) (by positivity)
      (pow_le_pow_right₀ hR (by decide : 40 ≤ 70))
  have hC' : C*N^s/(N^k)^60 ≤ C*N^s/(N^k)^40 :=
    div_le_div_of_nonneg_left (by positivity) (by positivity)
      (pow_le_pow_right₀ hR (by decide : 40 ≤ 60))
  calc
    _ ≤ A*N^s/(N^k)^40+B*N^s/(N^k)^40+C*N^s/(N^k)^40+D*N^s/(N^k)^40 :=
      add_le_add (add_le_add (add_le_add le_rfl hB') hC') le_rfl
    _ = (A+B+C+D)*N^s/(N^k)^40 := by ring
    _ ≤ N^q*N^s/(N^k)^40 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right (hconst N hN).2 (by positivity)
    _ ≤ 1/(N^k)^38 := by
      rw [div_le_div_iff₀ (pow_pos (pow_pos hN0 k) _) (pow_pos (pow_pos hN0 k) _),
        one_mul,← pow_add,← pow_mul,← pow_add,← pow_mul]
      exact pow_le_pow_right₀ hN1 (by omega)
    _ = _ := by simp only [one_div,inv_pow,← pow_mul,Nat.mul_assoc]

theorem exists_four_residual_norm_power (A B C D : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D) (s : ℕ) :
    ∃ k₀ : ℕ, 1 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k → ∀ N : ℝ, 2 ≤ N →
      A*N^s/(N^k)^40+B*N^s/(N^k)^70+C*N^s/(N^k)^60+D*N^s/(N^k)^40 ≤
        ((N^k)^19)⁻¹^2 := by
  obtain ⟨q,hq,hbound⟩ := exists_four_residual_norm_offset A B C D hA hB hC hD
  exact ⟨q+s,by omega,fun k hk => hbound s k hk⟩

end ContinuumCoulomb

end

end OAI
