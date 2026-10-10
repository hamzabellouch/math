import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace OAI

/-! # A strict curvature margin supplies the small-mesh comparison coefficient -/

open Set Filter
open scoped Topology
namespace RegularPointCoordinates

theorem one_add_half_sq_le_cosh (x : ℝ) : 1+x^2/2 ≤ Real.cosh x := by
  have hp (i : ℕ) : 0 ≤ x^(2*i)/(Nat.factorial (2*i):ℝ) := by
    rw [pow_mul]
    positivity
  have h : (∑ i ∈ Finset.range 2, x^(2*i)/(Nat.factorial (2*i):ℝ)) ≤
      ∑' i : ℕ, x^(2*i)/(Nat.factorial (2*i):ℝ) :=
    (Real.hasSum_cosh x).summable.sum_le_tsum (Finset.range 2) (fun i _ => hp i)
  rw [←Real.cosh_eq_tsum] at h
  simpa [Finset.sum_range_succ] using h

theorem gaussian_factor_cosh_ge_one {c q h : ℝ} (hc : 0 < c)
    (hsmall₀ : h^2 ≤ 2/c) (hsmall₁ : h^2 ≤ 2*(q^2-c)/c^2) :
    1 ≤ Real.exp (-c*h^2/2)*Real.cosh (q*h) := by
  let z := c*h^2/2
  have hz0 : 0 ≤ z := by dsimp [z]; positivity
  have hz1 : z ≤ 1 := by
    have hh := (le_div_iff₀ hc).mp hsmall₀
    dsimp only [z]
    nlinarith
  have hex := Real.abs_exp_sub_one_sub_id_le (x:=z) (by simpa only [abs_of_nonneg hz0] using hz1)
  have hex' : Real.exp z ≤ 1+z+z^2 := by linarith [(le_abs_self (Real.exp z-1-z)).trans hex]
  have hsq := (le_div_iff₀ (sq_pos_of_pos hc)).mp hsmall₁
  have hmargin : z^2 ≤ (q^2-c)*h^2/2 := by
    have hh := mul_le_mul_of_nonneg_right hsq (sq_nonneg h)
    dsimp only [z]
    nlinarith only [hh]
  have he : Real.exp z ≤ Real.cosh (q*h) := by
    have hh := one_add_half_sq_le_cosh (q*h)
    have hz : z+(q^2-c)*h^2/2=(q*h)^2/2 := by dsimp [z]; ring
    linarith only [hex',hmargin,hh,hz]
  have hcancel : Real.exp (-z)*Real.exp z=1 := by rw [←Real.exp_add]; simp
  have hm := mul_le_mul_of_nonneg_left he (Real.exp_pos (-z)).le
  rw [hcancel] at hm
  simpa only [z, neg_div, neg_mul] using hm

theorem eventually_gaussian_cosh_comparison {c q : ℝ} (hc : 0 < c) (hq : c < q^2) :
    ∀ᶠ h : ℝ in 𝓝 0, 1 ≤ Real.exp (-c*h^2/2)*Real.cosh (q*h) := by
  have h₀ : 0 < 2/c := div_pos (by norm_num) hc
  have h₁ : 0 < 2*(q^2-c)/c^2 := div_pos (mul_pos (by norm_num) (sub_pos.mpr hq)) (sq_pos_of_pos hc)
  have hlim : Tendsto (fun h : ℝ => h^2) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun h : ℝ => h^2) := continuous_id.pow 2
    simpa using hc.tendsto 0
  filter_upwards [hlim.eventually (gt_mem_nhds h₀),hlim.eventually (gt_mem_nhds h₁)] with h ha hb
  exact gaussian_factor_cosh_ge_one hc ha.le hb.le

end RegularPointCoordinates

end OAI
