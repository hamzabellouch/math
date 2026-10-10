import OAI.Analysis.LipschitzHilbert.Estimates.SharpRemainderDecay

namespace OAI

/-! Elementary uniform logarithmic weights for the three restricted
regimes. The exponential estimate is global and uses 1+x <= exp x. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

theorem exponential_log_weight (b : ℝ) (hb : 0<b) :
    ∃ C : ℝ, 0<C ∧ ∀ x : ℝ, 0≤x →
      Real.exp (-b*x)≤C*((1+x)^3)⁻¹ := by
  let M := 1+3/b
  have hM : 0<M := by dsimp [M]; positivity
  refine ⟨M^3,pow_pos hM _,?_⟩
  intro x hx
  have hfirst : 1+x≤M*Real.exp (b*x/3) := by
    calc
      1+x ≤ 1+3/b+x+b*x/3 := by
        have h1 : 0≤3/b := by positivity
        have h2 : 0≤b*x/3 := by positivity
        linarith only [h1,h2]
      _ = M*(1+b*x/3) := by dsimp [M]; field_simp; ring
      _ ≤ M*Real.exp (b*x/3) := mul_le_mul_of_nonneg_left
        (by simpa only [add_comm] using Real.add_one_le_exp (b*x/3)) hM.le
  have hp := pow_le_pow_left₀ (by positivity : 0≤1+x) hfirst 3
  have hexp : (Real.exp (b*x/3))^3=Real.exp (b*x) := by
    rw [←Real.exp_nat_mul]
    congr 1
    ring
  rw [mul_pow,hexp] at hp
  have hprod : Real.exp (-b*x)*(1+x)^3≤M^3 := by
    calc
      _ ≤ Real.exp (-b*x)*(M^3*Real.exp (b*x)) :=
        mul_le_mul_of_nonneg_left hp (Real.exp_pos _).le
      _ = _ := by rw [mul_left_comm,←Real.exp_add]; simp
  rw [←div_eq_mul_inv]
  exact (le_div_iff₀ (by positivity : 0<(1+x)^3)).2 hprod

theorem high_log_weight (L : ℝ) (hL : 1≤L) :
    L^(-19:ℝ)≤27*((1+2*L)^3)⁻¹ := by
  have hLp : 0<L := zero_lt_one.trans_le hL
  calc
    L^(-19:ℝ) ≤ L^(-3:ℝ) := Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
    _ = 1/L^3 := by rw [Real.rpow_neg hLp.le]; norm_num [Real.rpow_natCast,one_div]
    _ ≤ 27/(1+2*L)^3 := by
      apply (div_le_div_iff₀ (pow_pos hLp _) (by positivity)).2
      have h := pow_le_pow_left₀ (by positivity : 0≤1+2*L)
        (show 1+2*L≤3*L by linarith only [hL]) 3
      simpa only [one_mul,mul_pow,show (3:ℝ)^3=27 by norm_num] using h
    _ = _ := by rw [div_eq_mul_inv]

theorem bounded_log_weight (x R : ℝ) (hx : 0≤x) (hxR : x≤R) :
    1≤(1+R)^3*((1+x)^3)⁻¹ := by
  rw [←div_eq_mul_inv]
  apply (one_le_div (by positivity : 0<(1+x)^3)).2
  exact pow_le_pow_left₀ (by positivity) (by linarith only [hxR]) 3

end LipschitzHilbert.PacketRepresentation

end

end OAI
