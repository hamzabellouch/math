import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialUniformExteriorPressure
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPhysicalAsymptotic

namespace OAI

/-! Uniform comparison of the actual mass weight with the Japanese-bracket weight. -/

open Set Filter
namespace DefocusingNLS
open ProfileCertificate

theorem radial_bracket_weight_comparison (s α : ℝ) (hs : 1 ≤ s)
    (hα : α ∈ Icc 0 2) :
    (1+s)^(-α) ≤ s^(-α) ∧ s^(-α) ≤ 4*(1+s)^(-α) := by
  have hsp : 0 < s := lt_of_lt_of_le zero_lt_one hs
  refine ⟨Real.rpow_le_rpow_of_nonpos hsp (by linarith) (neg_nonpos.mpr hα.1),?_⟩
  have htwo : (2 : ℝ)^α ≤ 4 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hα.2
    norm_num [Real.rpow_ofNat] at hh
    exact hh
  have hm : (2*s)^(-α) ≤ (1+s)^(-α) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (neg_nonpos.mpr hα.1)
  calc
    s^(-α)=2^α*(2*s)^(-α) := by
      rw [Real.mul_rpow (by norm_num) hsp.le,← mul_assoc,← Real.rpow_add (by norm_num)]
      simp
    _ ≤ 4*(1+s)^(-α) := mul_le_mul htwo hm (Real.rpow_nonneg (by positivity) _) (by norm_num)

theorem radialMatched_exterior_weight (n : ℕ) (z : ProfileMatchingBall)
    (r : ℝ) (hr : innerBoundaryRadius < r) :
    let m := n+radialInnerShootingThreshold
    let Z := radialExteriorCanonical (radialShootingNu m z) m (radialShootingM z)
      (Real.log innerBoundaryRadius)
    ‖radialMatchedProfile n z r‖^2=(r^2)^(-2*radialShootingA n)*‖(Z (Real.log r)).1‖^2 := by
  intro m Z
  have hrp : 0 < r := lt_trans (by linarith [innerBoundaryRadius_bounds.1]) hr
  have hν : (radialShootingNu m z).re= -2*radialShootingA n := by
    change (radialShootingNu (n+radialInnerShootingThreshold) z).re= -2*radialShootingA n
    rw [radialShootingNu_physical]
    simp [Complex.mul_re,Complex.mul_im]
  have hv : ‖radialMatchedProfile n z r‖=r^(-2*radialShootingA n)*‖(Z (Real.log r)).1‖ := by
    simp only [radialMatchedProfile,ite_eq_right hr.not_ge,radialShootingExteriorProfile,
      radialPhysicalExterior,norm_mul,radialPhysicalFactor_norm _ _ hrp]
    change r^(radialShootingNu m z).re*‖(Z (Real.log r)).1‖=_
    rw [hν]
  have hp : (r^(-2*radialShootingA n))^2=(r^2)^(-2*radialShootingA n) := by
    rw [← Real.rpow_mul_natCast hrp.le _ 2,← Real.rpow_natCast_mul hrp.le 2 _]
    congr 1
    ring
  rw [hv,mul_pow,hp]

theorem radialMatched_uniform_weight_comparison :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop, ∀ z : ProfileMatchingBall,
      ∀ r : ℝ, 0 ≤ r →
        c*(1+r^2)^(-2*radialShootingA n) ≤ ‖radialMatchedProfile n z r‖^2 ∧
        ‖radialMatchedProfile n z r‖^2 ≤ 144*(1+r^2)^(-2*radialShootingA n) := by
  obtain ⟨κ,ρ,hκ,hρ,hann⟩ := radialShooting_uniform_annulus
  refine ⟨min (κ^2) ((999/1000 : ℝ)^2),lt_min (sq_pos_of_pos hκ) (by norm_num),?_⟩
  let N := fun n : ℕ => n+radialInnerShootingThreshold
  have hN : StrictMono N := fun _ _ hij => Nat.add_lt_add_right hij _
  filter_upwards [hN.tendsto_atTop.eventually hann] with n hn z r hr
  have ha := radialShootingA_bounds n (profileMatchingParameter z)
  have hα : 2*radialShootingA n ∈ Icc (0 : ℝ) 2 := ⟨by linarith,by linarith⟩
  have hw0 : 0 ≤ (1+r^2)^(-2*radialShootingA n) := Real.rpow_nonneg (by positivity) _
  by_cases hi : r ≤ innerBoundaryRadius
  · have hA := (radialMatchedAmplitude_inner_bounds n z r ⟨hr,hi⟩).1
    have hAsq : (999/1000 : ℝ)^2 ≤ ‖radialMatchedProfile n z r‖^2 :=
      (sq_le_sq₀ (by norm_num) (norm_nonneg _)).mpr hA.1
    have hAsq1 : ‖radialMatchedProfile n z r‖^2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hA.2
    have hw1 : (1+r^2)^(-2*radialShootingA n) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg r]) (by linarith)
    have hsize : 1+r^2 ≤ 12 := by
      have hh := innerBoundaryRadius_bounds.2
      have hs := (sq_le_sq₀ hr (le_trans hr hi)).mpr hi
      nlinarith
    have hwl : (1/144 : ℝ) ≤ (1+r^2)^(-2*radialShootingA n) := by
      have h1 : (12 : ℝ)^(-2 : ℝ) ≤ (1+r^2)^(-2 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hsize (by norm_num)
      have h2 : (1+r^2)^(-2 : ℝ) ≤ (1+r^2)^(-2*radialShootingA n) :=
        Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg r]) (by linarith)
      norm_num at h1 h2
      simpa only [neg_mul] using h1.trans h2
    constructor
    · exact (mul_le_mul_of_nonneg_right (min_le_right _ _) hw0).trans
        ((mul_le_of_le_one_right (sq_nonneg _) hw1).trans hAsq)
    · nlinarith
  · have hrb : innerBoundaryRadius < r := lt_of_not_ge hi
    have hrp : 0 < r := lt_trans (by linarith [innerBoundaryRadius_bounds.1]) hrb
    have hr2 : 1 ≤ r^2 := by nlinarith [innerBoundaryRadius_bounds.1]
    have hf := hn z (Real.log r) (Real.log_le_log
      (by linarith [innerBoundaryRadius_bounds.1]) hrb.le)
    have hw := radial_bracket_weight_comparison (r^2) (2*radialShootingA n) hr2 hα
    simp only [← neg_mul] at hw
    have hflo : κ^2 ≤ ‖(radialExteriorCanonical (radialShootingNu (N n) z) (N n)
        (radialShootingM z) (Real.log innerBoundaryRadius) (Real.log r)).1‖^2 :=
      (sq_le_sq₀ hκ.le (norm_nonneg _)).mpr hf.1
    have hfhi : ‖(radialExteriorCanonical (radialShootingNu (N n) z) (N n)
        (radialShootingM z) (Real.log innerBoundaryRadius) (Real.log r)).1‖^2 ≤ 1 :=
      pow_le_one₀ (norm_nonneg _) (hf.2.trans hρ.le)
    rw [radialMatched_exterior_weight n z r hrb]
    constructor
    · calc
        _ ≤ κ^2*(1+r^2)^(-2*radialShootingA n) :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) hw0
        _ ≤ (r^2)^(-2*radialShootingA n)*κ^2 := by
          nlinarith [mul_le_mul_of_nonneg_right hw.1 (sq_nonneg κ)]
        _ ≤ _ := mul_le_mul_of_nonneg_left hflo (Real.rpow_nonneg (sq_nonneg _) _)
    · have hh := mul_le_of_le_one_right (Real.rpow_nonneg (sq_nonneg r) (-2*radialShootingA n)) hfhi
      exact hh.trans (hw.2.trans (by nlinarith))

end DefocusingNLS

end OAI
