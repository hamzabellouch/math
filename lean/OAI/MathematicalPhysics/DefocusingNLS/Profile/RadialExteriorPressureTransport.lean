import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialUniformJet
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialUniformExteriorPressure
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorPressureDerivative
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedPressureTransport

namespace OAI

/-! Uniform smallness of the exterior pressure transported by the actual velocity. -/

open Set Filter
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatched_exterior_pressure_transport_small (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ z : ProfileMatchingBall,
      HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
        (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius) →
      radialMatchingMap n z=0 → ∀ r : ℝ, innerBoundaryRadius < r →
        r^2*|radialVelocity (6-2*radialShootingA n) (fun t => ‖radialMatchedProfile n z t‖) r*
          deriv (fun t => ‖radialMatchedProfile n z t‖^(2*(n+radialInnerShootingThreshold))/
            radialShootingA n) r| < ε := by
  obtain ⟨κ,ρ,hκ,hρ,hann⟩ := radialShooting_uniform_annulus
  obtain ⟨B,hB,hjet⟩ := radialShooting_uniform_jet_bound
  let C := B/κ
  let K := 3+2*C
  let q := max ρ 0
  have hC : 0 ≤ C := div_nonneg hB.le hκ.le
  have hK : 0 < K := by dsimp [K]; linarith
  have hC1 : 0 ≤ 1+C := add_nonneg zero_le_one hC
  have hq : 0 ≤ q := le_max_right _ _
  have hq1 : q < 1 := max_lt hρ (by norm_num)
  have hq2 : q^2 < 1 := by nlinarith
  let N := fun n : ℕ => n+radialInnerShootingThreshold
  have hN : StrictMono N := fun _ _ hij => Nat.add_lt_add_right hij _
  have hdecay : Tendsto (fun n => 4*K*(1+C)*((N n : ℝ)^2*(q^2)^(N n)))
      atTop (nhds 0) := by
    simpa only [mul_zero,Function.comp_def] using
      ((tendsto_pow_const_mul_const_pow_of_lt_one 2 (sq_nonneg q) hq2).comp
        hN.tendsto_atTop).const_mul (4*K*(1+C))
  filter_upwards [hN.tendsto_atTop.eventually hann,hN.tendsto_atTop.eventually hjet,
    hdecay.eventually (gt_mem_nhds hε)] with n hn hj he z hX hz r hr
  let m := N n
  let ν := radialShootingNu m z
  let Z := radialExteriorCanonical ν m (radialShootingM z) (Real.log innerBoundaryRadius)
  let ξ := (Z (Real.log r)).2/(Z (Real.log r)).1
  let P := fun t => ‖radialMatchedProfile n z t‖^(2*m)/radialShootingA n
  let w := radialVelocity (6-2*radialShootingA n) (fun t => ‖radialMatchedProfile n z t‖)
  have hrp : 0 < r := lt_trans (by linarith [innerBoundaryRadius_bounds.1]) hr
  have hr2 : 1 ≤ r^2 := by nlinarith [innerBoundaryRadius_bounds.1]
  have hm : (1 : ℝ) ≤ m := by
    exact_mod_cast (le_trans (by norm_num) (radialShootingIndex_large n z))
  have hlog : Real.log innerBoundaryRadius ≤ Real.log r :=
    Real.log_le_log (by linarith [innerBoundaryRadius_bounds.1]) hr.le
  have hf := hn z (Real.log r) hlog
  have hZ : ‖Z (Real.log r)‖ ≤ B := hj z (Real.log r) hlog
  have hξ : ‖ξ‖ ≤ C := by
    rw [show ξ=(Z (Real.log r)).2/(Z (Real.log r)).1 from rfl,norm_div]
    exact div_le_div₀ hB.le ((norm_snd_le _).trans hZ) hκ hf.1
  have hξre : |ξ.re| ≤ C := (Complex.abs_re_le_norm ξ).trans hξ
  have hξim : |ξ.im| ≤ C := (Complex.abs_im_le_norm ξ).trans hξ
  have hνim : |ν.im| ≤ 1 := by
    have hg := (radialShooting_geometry (profileMatchingParameter z)).1
    have hν : ν.im=2*radialShootingB (profileMatchingParameter z) := by
      simp [ν,radialShootingNu,radialShootingQ,Complex.mul_im,Complex.mul_re]
    rw [hν,abs_of_nonneg (by linarith [hg.1])]
    linarith [hg.2]
  have hsum : |ν.im+ξ.im| ≤ 1+C :=
    (abs_add_le _ _).trans (add_le_add hνim hξim)
  have hquot0 : 0 ≤ 2/r^2 := div_nonneg (by norm_num) (sq_nonneg r)
  have hquot : 2/r^2 ≤ (2 : ℝ) := (div_le_iff₀ (sq_pos_of_pos hrp)).mpr (by nlinarith)
  have hm0 : 0 ≤ 2*(m : ℝ) := mul_nonneg (by norm_num) (Nat.cast_nonneg _)
  have hvel : |w r/r| ≤ K := by
    rw [radialMatchedVelocity_logarithmic n z hX hz r hr]
    calc
      |1/2+2/r^2*(ν.im+ξ.im)| ≤ |(1/2 : ℝ)|+|2/r^2*(ν.im+ξ.im)| := abs_add_le _ _
      _ = 1/2+(2/r^2)*|ν.im+ξ.im| := by
        rw [abs_mul,abs_of_nonneg (show 0 ≤ (1/2 : ℝ) by norm_num),abs_of_nonneg hquot0]
      _ ≤ 1/2+(2/r^2)*(1+C) := add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hsum hquot0)
      _ ≤ 1/2+2*(1+C) := add_le_add le_rfl
        (mul_le_mul_of_nonneg_right hquot hC1)
      _ ≤ K := by dsimp [K]; linarith
  have hfac : |-2+2*(m : ℝ)*ξ.re| ≤ 2*(m : ℝ)*(1+C) := by
    calc
      |-2+2*(m : ℝ)*ξ.re| ≤ |(-2 : ℝ)|+|2*(m : ℝ)*ξ.re| := abs_add_le _ _
      _ = 2+2*(m : ℝ)*|ξ.re| := by rw [abs_mul,abs_of_nonneg hm0]; norm_num
      _ ≤ 2+2*(m : ℝ)*C := add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hξre hm0)
      _ ≤ 2*(m : ℝ)*(1+C) := by nlinarith
  have hP : 0 ≤ P r := div_nonneg (by positivity)
    (radialShootingA_bounds n (profileMatchingParameter z)).1.le
  have hPb : r^2*P r ≤ 2*(m : ℝ)*q^(2*m) := by
    rw [radialMatched_exterior_pressure n z r hr]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _)
      (hf.2.trans (le_max_left _ _)) _) (by positivity)
  have hd : r*deriv P r=P r*(-2+2*(m : ℝ)*ξ.re) :=
    radialMatched_exterior_pressure_derivative n z hX hz r hr
  have hdw : w r*deriv P r=(w r/r)*P r*(-2+2*(m : ℝ)*ξ.re) := by
    calc
      w r*deriv P r=(w r/r)*(r*deriv P r) := by field_simp [hrp.ne']
      _ = (w r/r)*P r*(-2+2*(m : ℝ)*ξ.re) := by rw [hd]; ring
  change r^2*|w r*deriv P r| < ε
  rw [hdw,abs_mul,abs_mul,abs_of_nonneg hP]
  calc
    r^2*(|w r/r| * P r*|-2+2*(m : ℝ)*ξ.re|) ≤
        r^2*(K*P r*(2*(m : ℝ)*(1+C))) := by gcongr
    _ = (r^2*P r)*K*(2*(m : ℝ)*(1+C)) := by ring
    _ ≤ (2*(m : ℝ)*q^(2*m))*K*(2*(m : ℝ)*(1+C)) := by gcongr
    _ = 4*K*(1+C)*((m : ℝ)^2*(q^2)^m) := by rw [pow_mul]; ring
    _ < ε := he

theorem radialMatched_global_pressure_transport_bound :
    ∀ᶠ n in atTop, ∀ z : ProfileMatchingBall,
      HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
        (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius) →
      radialMatchingMap n z=0 → ∀ r : ℝ, 0 ≤ r →
        radialVelocity (6-2*radialShootingA n) (fun t => ‖radialMatchedProfile n z t‖) r*
          deriv (fun t => ‖radialMatchedProfile n z t‖^(2*(n+radialInnerShootingThreshold))/
            radialShootingA n) r ≤ 1600 := by
  filter_upwards [radialMatched_exterior_pressure_transport_small 1 (by norm_num)]
    with n hn z hX hz r hr
  by_cases hi : r ≤ innerBoundaryRadius
  · have hd := radialMatchedInnerPressure_transport n z hX hz r ⟨hr,hi⟩
    have hp := (radialMatchedAmplitude_inner_bounds n z r ⟨hr,hi⟩).2
    exact hd.trans (by nlinarith)
  · have hlarge := hn z hX hz r (lt_of_not_ge hi)
    have hr2 : 1 ≤ r^2 := by nlinarith [innerBoundaryRadius_bounds.1]
    have ha := abs_nonneg (radialVelocity (6-2*radialShootingA n)
      (fun t => ‖radialMatchedProfile n z t‖) r*
      deriv (fun t => ‖radialMatchedProfile n z t‖^(2*(n+radialInnerShootingThreshold))/
        radialShootingA n) r)
    have hh := le_abs_self (radialVelocity (6-2*radialShootingA n)
      (fun t => ‖radialMatchedProfile n z t‖) r*
      deriv (fun t => ‖radialMatchedProfile n z t‖^(2*(n+radialInnerShootingThreshold))/
        radialShootingA n) r)
    nlinarith

end DefocusingNLS

end OAI
