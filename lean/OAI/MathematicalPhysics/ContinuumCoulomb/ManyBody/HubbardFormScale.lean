import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedHubbardForm
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.OneBodyScaleBudget
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ScalarScaleBudgets

namespace OAI

/-! Polynomial accumulation of the actual one- and two-body entry errors. -/

noncomputable section
namespace ContinuumCoulomb

theorem localizedHubbardFormError_polynomial (m : ℕ) (freq D ε z : ℝ)
    (hz : Real.exp (-(9/10:ℝ)*D) ≤ z) :
    localizedHubbardFormError m freq D ε ≤
      4*(m+1:ℝ)^2*ε+
      (512*planarOverlapConstant*localizedPotentialBound freq+8*localizedFourIndexConstant freq)*
        (m+1:ℝ)^9*z := by
  have hO := planarOverlapConstant_nonnegative
  have hP := localizedPotentialBound_nonnegative freq
  have hC := localizedFourIndexConstant_nonnegative freq
  have hm : 1 ≤ (m+1:ℝ) := by have := Nat.cast_nonneg (α := ℝ) m; linarith
  have hpow : (m+1:ℝ)^4 ≤ (m+1:ℝ)^9 := pow_le_pow_right₀ hm (by decide)
  have hc := mul_le_mul_of_nonneg_left hpow
    (show 0 ≤ 8*localizedFourIndexConstant freq by positivity)
  have he := mul_le_mul_of_nonneg_left hz
    (show 0 ≤ 512*planarOverlapConstant*localizedPotentialBound freq*(m+1:ℝ)^9+
      8*localizedFourIndexConstant freq*(m+1:ℝ)^9 by positivity)
  have hid : localizedHubbardFormError m freq D ε =
      4*(m+1:ℝ)^2*ε+
      (512*planarOverlapConstant*localizedPotentialBound freq*(m+1:ℝ)^9+
        8*localizedFourIndexConstant freq*(m+1:ℝ)^4)*Real.exp (-(9/10:ℝ)*D) := by
    unfold localizedHubbardFormError localizedOverlapBound
    ring
  rw [hid]
  refine add_le_add le_rfl ?_
  calc
    _ ≤ (512*planarOverlapConstant*localizedPotentialBound freq*(m+1:ℝ)^9+
        8*localizedFourIndexConstant freq*(m+1:ℝ)^9)*Real.exp (-(9/10:ℝ)*D) :=
      mul_le_mul_of_nonneg_right (add_le_add le_rfl hc) (Real.exp_pos _).le
    _ ≤ _ := he.trans_eq (by ring)

theorem exists_hubbardForm_parameter_offset (freq : ℝ) :
    ∃ k₀ : ℕ, 1 ≤ k₀ ∧ ∀ r p k : ℕ, k₀+9*r+p ≤ k →
      ∀ N D : ℝ, 2 ≤ N → 25*(k:ℝ)*Real.log N ≤ D →
      ∀ m : ℕ, (m+1:ℝ) ≤ N^r →
      localizedHubbardFormError m freq D ((N^(2*r+p+3))⁻¹) ≤ (N^p)⁻¹ := by
  let C := 512*planarOverlapConstant*localizedPotentialBound freq+8*localizedFourIndexConstant freq
  have hC : 0 ≤ C := add_nonneg (mul_nonneg (mul_nonneg (by norm_num)
    planarOverlapConstant_nonnegative) (localizedPotentialBound_nonnegative freq))
    (mul_nonneg (by norm_num) (localizedFourIndexConstant_nonnegative freq))
  obtain ⟨q,hq,hbound⟩ := exists_polynomial_ratio_offset C (by norm_num : (0:ℝ)<1/2)
  refine ⟨q,hq,fun r p k hk N D hN hD m hm => ?_⟩
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hR1 : 1 ≤ N^k := one_le_pow₀ hN1
  have hfirst : 4*(m+1:ℝ)^2*(N^(2*r+p+3))⁻¹ ≤ (1/2:ℝ)/N^p := by
    calc
      _ ≤ 4*(N^r)^2*(N^(2*r+p+3))⁻¹ := by gcongr
      _ = (4/N^3)/N^p := by
        rw [pow_add,pow_add,show 2*r=r*2 by omega,pow_mul]
        field_simp
      _ ≤ _ := div_le_div_of_nonneg_right
        ((div_le_iff₀ (pow_pos hN0 3)).mpr (by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) hN 3]))
        (by positivity)
  have hsecond : C*(m+1:ℝ)^9*((N^k)^22)⁻¹ ≤ (1/2:ℝ)/N^p := by
    calc
      _ ≤ C*N^(9*r)/(N^k)^2 := by
        rw [inv_eq_one_div,mul_one_div]
        gcongr
        · rw [show 9*r=r*9 by omega,pow_mul]
          exact pow_le_pow_left₀ (by positivity) hm 9
        · decide
      _ ≤ _ := hbound (9*r) p k hk N hN
  have he := localizedHubbardFormError_polynomial m freq D ((N^(2*r+p+3))⁻¹)
    (((N^k)^22)⁻¹) (logarithmic_separation_overlap hN k hD)
  exact he.trans ((add_le_add hfirst hsecond).trans_eq (by rw [one_div]; ring))

end ContinuumCoulomb

end

end OAI
