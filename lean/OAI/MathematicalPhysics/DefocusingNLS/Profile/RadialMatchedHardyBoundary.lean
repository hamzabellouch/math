import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialHardyBoundary
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialWeightComparison

namespace OAI

/-! The uniform Hardy estimate with the actual mass density of matched profiles. -/

open Set Filter
open scoped ContDiff
namespace DefocusingNLS
open ProfileCertificate

theorem radialHardy_comparable_weight_boundary (a R d : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1/2)
    (hR : 0 ≤ R) (hd : 0 < d) (μ : ℝ → ℝ) (hμ : Continuous μ)
    (hb : ∀ r ∈ Icc 0 R,
      d*radialHardyWeight a r ≤ μ r ∧ μ r ≤ 144*radialHardyWeight a r)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) :
    d*(∫ r in (0 : ℝ)..R, r^9*μ r*(f r)^2) ≤
      9*(∫ r in (0 : ℝ)..R, r^11*μ r*(deriv f r)^2)+
        36*d*radialHardyFlux a R*(f R)^2 := by
  have hρ := radialHardyWeight_continuous a
  have hfd := hf.continuous_deriv_one
  have hA : Continuous (fun r => r^9*μ r*(f r)^2) := by fun_prop
  have hB : Continuous (fun r => r^11*μ r*(deriv f r)^2) := by fun_prop
  have hAρ : Continuous (fun r => r^9*radialHardyWeight a r*(f r)^2) := by fun_prop
  have hBρ : Continuous (fun r => r^11*radialHardyWeight a r*(deriv f r)^2) := by fun_prop
  have hupper : (∫ r in (0 : ℝ)..R, r^9*μ r*(f r)^2) ≤
      144*(∫ r in (0 : ℝ)..R, r^9*radialHardyWeight a r*(f r)^2) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hR (hA.intervalIntegrable 0 R)
      ((hAρ.const_mul 144).intervalIntegrable 0 R)
    intro r hr
    have hh := mul_le_mul_of_nonneg_left (hb r hr).2
      (mul_nonneg (pow_nonneg hr.1 9) (sq_nonneg (f r)))
    nlinarith [hh]
  have hlower : d*(∫ r in (0 : ℝ)..R, r^11*radialHardyWeight a r*(deriv f r)^2) ≤
      ∫ r in (0 : ℝ)..R, r^11*μ r*(deriv f r)^2 := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hR ((hBρ.const_mul d).intervalIntegrable 0 R)
      (hB.intervalIntegrable 0 R)
    intro r hr
    have hh := mul_le_mul_of_nonneg_left (hb r hr).1
      (mul_nonneg (pow_nonneg hr.1 11) (sq_nonneg (deriv f r)))
    nlinarith [hh]
  have hhardy := radialHardyInequality_boundary a R ha ha1 hR f hf
  have hu := mul_le_mul_of_nonneg_left hupper hd.le
  have hh := mul_le_mul_of_nonneg_left hhardy (by positivity : 0 ≤ 9*d)
  nlinarith

theorem radialMatched_uniform_Hardy_boundary :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ n in atTop, ∀ z : ProfileMatchingBall,
      HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
        (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius) →
      radialMatchingMap n z=0 → ∀ R : ℝ, 0 ≤ R → ∀ f : ℝ → ℝ,
      ContDiff ℝ 1 f →
      d*(∫ r in (0 : ℝ)..R, r^9*‖radialMatchedProfile n z r‖^2*(f r)^2) ≤
        9*(∫ r in (0 : ℝ)..R, r^11*‖radialMatchedProfile n z r‖^2*(deriv f r)^2)+
          36*d*radialHardyFlux (radialShootingA n) R*(f R)^2 := by
  obtain ⟨d,hd,he⟩ := radialMatched_uniform_weight_comparison
  refine ⟨d,hd,?_⟩
  filter_upwards [he] with n hn z hX hz R hR f hf
  have ha := (radialShootingA_bounds n (profileMatchingParameter z)).1
  have hm : (1 : ℝ) ≤ ((n+radialInnerShootingThreshold : ℕ) : ℝ) := by
    exact_mod_cast radialShootingInner_power_pos n (profileMatchingParameter z)
  have ha1 : radialShootingA n ≤ 1/2 := by
    unfold radialShootingA
    apply (div_le_iff₀ (by linarith : (0 : ℝ)<2*((n+radialInnerShootingThreshold : ℕ) : ℝ))).mpr
    nlinarith
  apply radialHardy_comparable_weight_boundary (radialShootingA n) R d ha.le ha1 hR hd
    (fun r => ‖radialMatchedProfile n z r‖^2)
    ((radialMatchedProfile_differentiable n z hX hz).continuous.norm.pow 2)
    (fun r hr => hn z r hr.1) f hf

end DefocusingNLS

end OAI
