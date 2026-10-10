import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.HubbardFormScale

namespace OAI

/-! Combining the two entrywise approximation budgets in the finite form. -/

noncomputable section
namespace ContinuumCoulomb

theorem localizedHubbardFormError_mono (m : ℕ) (freq D : ℝ) {ε ε' : ℝ}
    (h : ε ≤ ε') :
    localizedHubbardFormError m freq D ε ≤ localizedHubbardFormError m freq D ε' := by
  unfold localizedHubbardFormError
  exact add_le_add (mul_le_mul_of_nonneg_left h (sq_nonneg _)) le_rfl

theorem double_inverse_power_le {N : ℝ} (hN : 2 ≤ N) (j : ℕ) :
    (N^(j+1))⁻¹+(N^(j+1))⁻¹ ≤ (N^j)⁻¹ := by
  have hN0 : 0 < N := by linarith
  rw [pow_succ]
  have hh : 2/(N^j*N) ≤ 1/N^j :=
    (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by nlinarith [pow_pos hN0 j])
  simpa only [div_eq_mul_inv,one_mul,two_mul] using hh

theorem exists_hubbardDouble_parameter_offset (freq : ℝ) :
    ∃ q : ℕ, 1 ≤ q ∧ ∀ r p k : ℕ, q+9*r+p ≤ k →
      ∀ N D : ℝ, 2 ≤ N → 25*(k:ℝ)*Real.log N ≤ D →
      ∀ m : ℕ, (m+1:ℝ) ≤ N^r →
      localizedHubbardFormError m freq D
        ((N^(2*r+p+6))⁻¹+(N^(2*r+p+6))⁻¹) ≤ (N^(p+2))⁻¹ := by
  obtain ⟨q,hq,hbound⟩ := exists_hubbardForm_parameter_offset freq
  refine ⟨q+2,by omega,fun r p k hk N D hN hD m hm => ?_⟩
  apply (localizedHubbardFormError_mono m freq D ?_).trans
    (hbound r (p+2) k (by omega) N D hN hD m hm)
  convert double_inverse_power_le hN (2*r+p+5) using 1

end ContinuumCoulomb

end

end OAI
