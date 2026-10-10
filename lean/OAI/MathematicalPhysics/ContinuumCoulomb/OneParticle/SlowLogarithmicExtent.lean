import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ContactExtent

namespace OAI

/-! The logarithmic spacing contributes only a hundredth of the adjustable
exponent. This closes the final analytic parameter inequalities without a
circular dependence on the spatial extent. -/

noncomputable section
namespace ContinuumCoulomb.ContactMediator

theorem hundred_mul_le_two_pow (q : ℕ) (hq : 11 ≤ q) : 100*(q+1) ≤ 2^q := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le hq
  induction r with
  | zero => norm_num
  | succ r ih =>
    calc
      100*(11+(r+1)+1) ≤ 2*(100*(11+r+1)) := by omega
      _ ≤ 2*2^(11+r) := Nat.mul_le_mul_left 2 (ih (by omega))
      _ = 2^(11+(r+1)) := by rw [show 11+(r+1)=11+r+1 by omega,pow_succ]; omega

theorem exponent_le_slow_power (k : ℕ) (hk : 1100 ≤ k) {N : ℝ} (hN : 2 ≤ N) :
    (k : ℝ) ≤ N^(k/100) := by
  have hq : 11 ≤ k/100 := by omega
  have hkn : k ≤ 100*(k/100+1) := by omega
  have hpow : (k : ℝ) ≤ (2:ℝ)^(k/100) := by
    exact_mod_cast hkn.trans (hundred_mul_le_two_pow _ hq)
  exact hpow.trans (pow_le_pow_left₀ (by norm_num) hN _)

theorem slow_logarithmic_extent (k s : ℕ) (hk : 1100 ≤ k)
    {N : ℝ} (hN : 2 ≤ N) :
    2*(31*(k:ℝ)*Real.log N)*(17*N^s+17) ≤ N^(k/100+s+13) := by
  have hNp : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hlog := (Real.log_le_sub_one_of_pos hNp).trans (show N-1 ≤ N by linarith)
  have hlog0 := Real.log_nonneg hN1
  have hsize : 17*N^s+17 ≤ 34*N^s := by nlinarith [one_le_pow₀ hN1 (n := s)]
  have hkpow := exponent_le_slow_power k hk hN
  have hC : (2108:ℝ) ≤ N^12 :=
    (by norm_num : (2108:ℝ) ≤ 2^12).trans (pow_le_pow_left₀ (by norm_num) hN 12)
  calc
    _ ≤ 2*(31*N^(k/100)*N)*(34*N^s) := by gcongr
    _ = 2108*(N^(k/100)*N^s*N) := by ring
    _ ≤ N^12*(N^(k/100)*N^s*N) := mul_le_mul_of_nonneg_right hC (by positivity)
    _ = N^(k/100+s+13) := by
      rw [show k/100+s+13=12+(k/100+s+1) by omega]
      simp only [pow_add,pow_one]

theorem slow_extent_parameter_closure (C k : ℕ) (hC : 4*C ≤ k) :
    C+72*(k/100) ≤ k := by omega

end ContinuumCoulomb.ContactMediator

end

end OAI
