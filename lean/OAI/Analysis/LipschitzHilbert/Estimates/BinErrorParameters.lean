import OAI.Analysis.LipschitzHilbert.Estimates.ShortTimeParameters

namespace OAI

/-! The manuscript's actual width and time scales absorb the cubic
width loss in the squared total bin error. -/
noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert

theorem eventually_cubic_width_short_time (D : ℝ) (hD : 0≤D) :
    ∀ᶠ L : ℝ in atTop, ∀ m tau : ℝ, 0≤m →
      m≤2*Real.exp (L^(9/10:ℝ)) → 0≤tau →
      tau≤Real.exp (-(L^(97/100:ℝ))) → D*m^3*tau^2≤L^(-40:ℝ) := by
  have hconstant : 0<4*(D+1) := by linarith
  filter_upwards [eventually_short_time_decay 40 hconstant,
    eventually_ge_atTop (1:ℝ),
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<7/100)).eventually_ge_atTop 2]
    with L hsmall hL hgap m tau hm hmb ht htb
  have hLp : 0<L := zero_lt_one.trans_le hL
  let a := L^(9/10:ℝ)
  let b := L^(97/100:ℝ)
  have hab : 2*a≤b := by
    have heq : b=a*L^(7/100:ℝ) := by
      dsimp only [a,b]
      rw [←Real.rpow_add hLp]
      norm_num
    rw [heq]
    nlinarith [Real.rpow_nonneg hLp.le (9/10:ℝ)]
  have hexp : (Real.exp a)^3*(Real.exp (-b))^2=Real.exp (3*a-2*b) := by
    rw [←Real.exp_nat_mul,←Real.exp_nat_mul,←Real.exp_add]
    congr 1
    ring
  have hdec : Real.exp (3*a-2*b)≤Real.exp (a-b) :=
    Real.exp_le_exp.mpr (by linarith)
  have hnumeric : 8*D*Real.exp (a-b)≤L^(-40:ℝ) := by
    have hpow : 0<L^(40:ℝ) := Real.rpow_pos_of_pos hLp _
    have hh : (8*D*Real.exp (a-b))*L^(40:ℝ)≤1 := by
      dsimp only [a,b]
      have hnonneg : 0≤L^(40:ℝ)*Real.exp (L^(9/10:ℝ)-L^(97/100:ℝ)) := by positivity
      nlinarith only [hsmall,hnonneg]
    rw [Real.rpow_neg hLp.le,←one_div]
    exact (le_div_iff₀ hpow).2 hh
  calc
    D*m^3*tau^2 ≤ D*(2*Real.exp a)^3*(Real.exp (-b))^2 :=
      mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hm hmb 3) hD)
        (pow_le_pow_left₀ ht htb 2) (sq_nonneg _) (by positivity)
    _ = 8*D*Real.exp (3*a-2*b) := by
      calc
        _ = 8*D*((Real.exp a)^3*(Real.exp (-b))^2) := by ring
        _ = _ := by rw [hexp]
    _ ≤ 8*D*Real.exp (a-b) := mul_le_mul_of_nonneg_left hdec (by positivity)
    _ ≤ _ := hnumeric

end LipschitzHilbert

end

end OAI
