import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import OAI.Geometry.NodalSets.Elliptic.RealEllipticLocalityLemmas

namespace OAI

namespace Yau.Geometry
open Filter MeasureTheory
open scoped Topology
noncomputable section

theorem exponential_integral_separation (F G phi : Yau.Jets.Coord → ℝ)
    (hF : Continuous F) (hG : Continuous G) (hphi : Continuous phi)
    (hcF : HasCompactSupport F) (hcG : HasCompactSupport G)
    (hF0 : ∀ x, 0 ≤ F x) (hG0 : ∀ x, 0 ≤ G x)
    (c T : ℝ) (hgap : ∀ x, G x ≠ 0 → phi x ≤ c)
    (hbound : ∀ t : ℝ, T ≤ t →
      (∫ x, Real.exp (t*phi x)*F x) ≤ (∫ x, Real.exp (t*phi x)*G x)) :
    ∀ y, c < phi y → F y = 0 := by
  intro y hy
  by_contra hFy
  let d := (c+phi y)/2
  have hcd : c < d := by dsimp [d]; linarith
  have hdy : d < phi y := by dsimp [d]; linarith
  let theta := fun x ↦ min 1 (max 0 (phi x-d))
  let H := fun x ↦ theta x*F x
  have htheta : Continuous theta := continuous_const.min (continuous_const.max (hphi.sub continuous_const))
  have ht0 (x) : 0 ≤ theta x := le_min zero_le_one (le_max_left _ _)
  have ht1 (x) : theta x ≤ 1 := min_le_left _ _
  have hH : Continuous H := htheta.mul hF
  have hcH : HasCompactSupport H := hcF.mul_left
  have hH0 (x) : 0 ≤ H x := mul_nonneg (ht0 x) (hF0 x)
  have hHy : H y ≠ 0 := mul_ne_zero (ne_of_gt (lt_min zero_lt_one
    (lt_max_of_lt_right (sub_pos.mpr hdy)))) hFy
  have hI : 0 < ∫ x, H x := hH.integral_pos_of_hasCompactSupport_nonneg_nonzero hcH hH0 hHy
  have hiH := hH.integrable_of_hasCompactSupport hcH (μ := volume)
  have hiG := hG.integrable_of_hasCompactSupport hcG (μ := volume)
  have hmain (t : ℝ) (ht : max T 0 ≤ t) :
      (∫ x, H x) ≤ Real.exp (-(d-c)*t)*(∫ x, G x) := by
    have ht0' : 0 ≤ t := (le_max_right _ _).trans ht
    have hiFt : Integrable (fun x ↦ Real.exp (t*phi x)*F x) :=  ((Real.continuous_exp.comp (continuous_const.mul hphi)).mul hF).integrable_of_hasCompactSupport
      hcF.mul_left (μ := volume)
    have hiGt : Integrable (fun x ↦ Real.exp (t*phi x)*G x) :=  ((Real.continuous_exp.comp (continuous_const.mul hphi)).mul hG).integrable_of_hasCompactSupport
      hcG.mul_left (μ := volume)
    have hlow (x) : Real.exp (t*d)*H x ≤ Real.exp (t*phi x)*F x := by
      by_cases hx : phi x ≤ d
      · have hzero : theta x = 0 := by simp [theta,max_eq_left (sub_nonpos.mpr hx)]
        change Real.exp (t*d)*(theta x*F x) ≤ _
        rw [hzero,zero_mul,mul_zero]
        exact mul_nonneg (Real.exp_pos _).le (hF0 x)
      · have he : Real.exp (t*d) ≤ Real.exp (t*phi x) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (not_le.mp hx).le ht0')
        calc
          _ ≤ Real.exp (t*d)*F x := mul_le_mul_of_nonneg_left
            (by dsimp [H]; nlinarith only [ht1 x,hF0 x]) (Real.exp_pos _).le
          _ ≤ _ := mul_le_mul_of_nonneg_right he (hF0 x)
    have hupp (x) : Real.exp (t*phi x)*G x ≤ Real.exp (t*c)*G x := by
      by_cases hx : G x = 0
      · simp [hx]
      · exact mul_le_mul_of_nonneg_right
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hgap x hx) ht0')) (hG0 x)
    have hl := integral_mono (hiH.const_mul (Real.exp (t*d))) hiFt hlow
    have hu := integral_mono hiGt (hiG.const_mul (Real.exp (t*c))) hupp
    rw [integral_const_mul] at hl hu
    have hb := hbound t ((le_max_left _ _).trans ht)
    have hh : Real.exp (t*d)*(∫ x, H x) ≤ Real.exp (t*c)*(∫ x, G x) := hl.trans (hb.trans hu)
    have heq : Real.exp (-(d-c)*t)*Real.exp (t*d) = Real.exp (t*c) := by
      rw [← Real.exp_add]; congr 1; ring
    apply (mul_le_mul_iff_right₀ (Real.exp_pos (t*d))).mp
    calc
      _ = Real.exp (t*d)*(∫ x, H x) := by ring
      _ ≤ Real.exp (t*c)*(∫ x, G x) := hh
      _ = _ := by rw [← heq]; ring
  have hdec : Tendsto (fun t : ℝ ↦ Real.exp (-(d-c)*t)*(∫ x, G x)) atTop (𝓝 0) := by
    have he := Real.tendsto_exp_atBot.comp
      ((tendsto_const_mul_atBot_of_neg (neg_neg_of_pos (sub_pos.mpr hcd))).mpr
        (tendsto_id : Tendsto (fun t : ℝ ↦ t) atTop atTop))
    simpa only [Function.comp_def,zero_mul,id_eq] using he.mul_const (∫ x, G x)
  have hle : (∫ x, H x) ≤ 0 := ge_of_tendsto hdec
    ((eventually_ge_atTop (max T 0)).mono (fun t ht ↦ hmain t ht))
  exact (not_le_of_gt hI) hle

end
end Yau.Geometry

end OAI
