import OAI.NumberTheory.TotientAsymptotic.SimplexExponential

namespace OAI

/-! Fixed positive volume survives a bounded loss in the scaled top budget. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma prefix_budget_power_lower {B E : ℝ} (hB : 0 < B) (hE : 0 ≤ E)
    (hEB : 2*E ≤ B) (N : ℕ) :
    Real.exp (-2*(N:ℝ)*E/B)*B^N ≤ (B-E)^N := by
  let q := E/B
  have hq : 0 ≤ q := div_nonneg hE hB.le
  have hq2 : q ≤ 1/2 := by
    apply (div_le_iff₀ hB).mpr
    linarith only [hEB]
  have hp : 0 < 1-q := by linarith only [hq2]
  have hlog : -2*q ≤ Real.log (1-q) := by
    have hh := log_one_add_quadratic_lower (x := -q) (by linarith only [hq2])
    have hs := mul_nonneg hq (show 0 ≤ 1/2-q by linarith only [hq2])
    have he : 1+(-q)=1-q := by ring
    rw [he] at hh
    nlinarith only [hh,hs]
  have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg N))
  simp only [Real.exp_nat_mul,Real.exp_log hp] at he
  have hfac := mul_le_mul_of_nonneg_right he (pow_nonneg hB.le N)
  have hid : B-E=(1-q)*B := by dsimp [q]; field_simp
  have hexp : Real.exp (-2*(N:ℝ)*E/B)=(Real.exp (-2*q))^N := by
    rw [←Real.exp_nat_mul]
    congr 1
    dsimp [q]
    ring
  rw [hid,mul_pow,hexp]
  exact hfac

end TotientAsymptotic

end

end OAI
