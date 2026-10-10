import OAI.MathematicalPhysics.Heisenberg.LayerRegularity

namespace OAI

noncomputable section
open scoped BigOperators
namespace Heisenberg.Clocks

lemma factorial_lower (r : ℕ) : ((r:ℝ)/Real.exp 1)^r ≤ (r.factorial:ℝ) := by
  by_cases hr : r=0
  · subst r; simp
  have hr1 : (1:ℝ)≤r := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hr)
  have hp : (1:ℝ)≤Real.sqrt (2*Real.pi*r) := by
    apply Real.one_le_sqrt.mpr
    nlinarith [Real.pi_gt_three]
  exact (le_mul_of_one_le_left (by positivity) hp).trans (Stirling.le_factorial_stirling r)

theorem clock_tail {N r : ℕ} {B δ : ℝ} (hB : 0≤B) (hδ : 0≤δ) (hr : 0<r)
    (hR : 4*Real.exp 1*B*((N+r:ℕ):ℝ)*δ ≤ r) :
    (((N+r).choose r:ℝ)*(2*B*δ)^r) ≤ (1/2:ℝ)^r := by
  have hrR : (0:ℝ)<r := by exact_mod_cast hr
  have hfac : (0:ℝ)<r.factorial := by positivity
  have he : (0:ℝ)<Real.exp 1 := Real.exp_pos _
  have hbase : 2*B*δ*((N+r:ℕ):ℝ)/((r:ℝ)/Real.exp 1) ≤ 1/2 := by
    apply (div_le_iff₀ (div_pos hrR he)).mpr
    rw [←mul_div_assoc]
    apply (le_div_iff₀ he).mpr
    nlinarith
  calc
    _ ≤ ((((N+r:ℕ):ℝ)^r)/(r.factorial:ℝ))*(2*B*δ)^r :=
      mul_le_mul_of_nonneg_right (Nat.choose_le_pow_div r (N+r)) (by positivity)
    _ = (2*B*δ*((N+r:ℕ):ℝ))^r/(r.factorial:ℝ) := by ring
    _ ≤ (2*B*δ*((N+r:ℕ):ℝ))^r/(((r:ℝ)/Real.exp 1)^r) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (factorial_lower r)
    _ = (2*B*δ*((N+r:ℕ):ℝ)/((r:ℝ)/Real.exp 1))^r := (div_pow _ _ _).symm
    _ ≤ _ := pow_le_pow_left₀ (by positivity) hbase r

end Heisenberg.Clocks

end

end OAI
