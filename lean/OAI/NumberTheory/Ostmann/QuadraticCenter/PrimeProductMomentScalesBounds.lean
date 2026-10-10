import OAI.NumberTheory.Ostmann.QuadraticCenter.PrimeProductMomentScalesAlgebra
import OAI.NumberTheory.Ostmann.QuadraticCenter.PrimeProductMomentScalesCosts

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Filter

theorem eventually_primeProduct_coefficient_bounds (c ε : ℝ) (hc : 0 < c) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ Z z : ℕ,
      T/2 ≤ Real.log Z → Real.log Z ≤ 2*T →
      1 ≤ z → T^auxiliaryExponent/2 ≤ Real.log z →
      Real.log z ≤ 2*T^auxiliaryExponent →
      ∀ F H J B : ℕ, F ≤ Z^430 → H ≤ 2*Z →
      c*(Z : ℝ)/Real.log Z ≤ J → B ≤ Z^14 →
      ∀ V : ℝ, 0 ≤ V → V ≤ (Z : ℝ)^430 →
      let k := evenMomentParameter (parameterX T) Z
      let l := gridMomentParameter T
      1 ≤ l ∧ 0 < J ∧ 2*k ≤ J ∧
      (F : ℝ)*2^l*((H : ℝ)^k+1)*(k.factorial : ℝ)*(2/(J : ℝ))^k ≤
        Real.exp (2*(l : ℝ)*ε*(auxiliaryK Z z : ℝ)) ∧
      (F : ℝ)*2^l*4*(B : ℝ)^(2*l)*V^(2*l)*(k.factorial : ℝ)*(2/(J : ℝ))^k ≤
        (Z : ℝ)^(-(20*(l : ℝ))) := by
  filter_upwards [eventually_primeProduct_moment_orders,
    eventually_primeProduct_probability_scale c hc,
    eventually_primeProduct_square_exponent ε hε] with T horders hprob hcost
  intro Z z hZl hZu hz hzl hzu F H J B hF hH hJ hB V hV0 hV
  dsimp only
  obtain ⟨hl,hkl,hkT⟩ := horders Z hZl hZu
  obtain ⟨hT,hTc,hlog,hZ,hsmall,hJscale⟩ := hprob Z hZl hZu
  obtain ⟨hJpos,hkJ⟩ := hJscale J hJ
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJpos
  have hk : 1 ≤ evenMomentParameter (parameterX T) Z := by omega
  have hFreal : (F : ℝ) ≤ (Z : ℝ)^430 := by exact_mod_cast hF
  have hHreal : (H : ℝ) ≤ 2*(Z : ℝ) := by exact_mod_cast hH
  have hBreal : (B : ℝ) ≤ (Z : ℝ)^14 := by exact_mod_cast hB
  have hsquare := primeMoment_square_coefficient_le
    (Nat.cast_nonneg F) (Nat.cast_nonneg H) hJr (by linarith : (1 : ℝ) ≤ Z)
    hT hl hk hc (by linarith : 0 < Real.log (Z : ℝ))
    hFreal hHreal hJ hZu hkT hTc
  have hnonsquare := primeMoment_nonsquare_coefficient_le
    (Nat.cast_nonneg F) (Nat.cast_nonneg B) hV0 hJr hZ hl hc
    (by linarith : 0 < Real.log (Z : ℝ)) hFreal hBreal hV hJ hsmall
  refine ⟨hl,hJpos,hkJ,hsquare.trans (Real.exp_le_exp.mpr (hcost Z z hZl hZu hz hzl hzu)),?_⟩
  have he := primeProduct_nonsquare_exponent (by linarith : 0 ≤ Real.log (Z : ℝ)) hl hkl
  calc
    _ ≤ Real.exp ((430+900*(gridMomentParameter T : ℝ))*Real.log (Z : ℝ)-
          ((evenMomentParameter (parameterX T) Z : ℝ)/2)*Real.log (Z : ℝ)) := hnonsquare
    _ ≤ Real.exp (-(20*(gridMomentParameter T : ℝ))*Real.log (Z : ℝ)) := Real.exp_le_exp.mpr he
    _ = _ := by
      rw [Real.rpow_def_of_pos (show (0 : ℝ) < Z by linarith)]
      congr 1
      ring

end Ostmann.QuadraticCenter

end

end OAI
