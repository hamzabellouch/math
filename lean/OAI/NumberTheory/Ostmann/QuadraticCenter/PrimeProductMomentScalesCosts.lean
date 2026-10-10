import OAI.NumberTheory.Ostmann.QuadraticCenter.PrimeProductMomentScalesGrowth

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Filter

theorem eventually_primeProduct_square_exponent (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ Z z : ℕ,
      T/2 ≤ Real.log Z → Real.log Z ≤ 2*T →
      1 ≤ z → T^auxiliaryExponent/2 ≤ Real.log z →
      Real.log z ≤ 2*T^auxiliaryExponent →
      430*Real.log Z+2*(gridMomentParameter T : ℝ)+
        3*(evenMomentParameter (parameterX T) Z : ℝ)*Real.log T ≤
      2*(gridMomentParameter T : ℝ)*ε*(auxiliaryK Z z : ℝ) := by
  filter_upwards [eventually_grid_cost_le (ε/860) (by positivity),
    eventually_moment_mul_log_le (ε/6) (by positivity),
    eventually_auxiliaryK_bounds,eventually_primeProduct_moment_orders,
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ)<3/4)).eventually_ge_atTop (4/ε)]
    with T hgrid hmoment hK horders hlarge
  intro Z z hZl hZu hz hzl hzu
  have hl : (1 : ℝ) ≤ gridMomentParameter T := by
    exact_mod_cast (horders Z hZl hZu).1
  have hlpos : (0 : ℝ) < gridMomentParameter T := by linarith
  have hg := (div_le_iff₀ hlpos).mp (hgrid Z z hZl hZu hz hzl hzu)
  have hm := hmoment Z z hZl hZu hz hzl hzu
  have hKlow := (hK Z z hZl hZu hz hzl hzu).1
  have hfixed : 4 ≤ ε*(auxiliaryK Z z : ℝ) := by
    have hh := (div_le_iff₀ hε).mp (hlarge.trans hKlow)
    nlinarith
  have hfixed' := mul_le_mul_of_nonneg_right hfixed (Nat.cast_nonneg (gridMomentParameter T))
  have hm' := mul_le_mul_of_nonneg_left hl
    (show 0 ≤ ε*(auxiliaryK Z z : ℝ) by positivity)
  nlinarith only [hg,hm,hfixed',hm']

theorem primeProduct_nonsquare_exponent {Z : ℝ} {k l : ℕ}
    (hZ : 0 ≤ Real.log Z) (hl : 1 ≤ l) (hkl : 4096*l ≤ k) :
    (430+900*(l : ℝ))*Real.log Z-((k : ℝ)/2)*Real.log Z ≤
      -(20*(l : ℝ))*Real.log Z := by
  have hlr : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hkr : (4096 : ℝ)*l ≤ k := by exact_mod_cast hkl
  have he : 430+900*(l : ℝ)-(k : ℝ)/2 ≤ -(20*(l : ℝ)) := by linarith
  have hh := mul_le_mul_of_nonneg_right he hZ
  nlinarith only [hh]

end Ostmann.QuadraticCenter

end

end OAI
