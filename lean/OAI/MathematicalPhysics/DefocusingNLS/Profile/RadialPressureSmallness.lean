import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorPressureTransport

namespace OAI

/-! Uniform smallness of the transported pressure in the form used by Hardy's inequality. -/

open Set Filter
namespace DefocusingNLS
open ProfileCertificate

theorem radialShootingA_tendsto_zero :
    Tendsto radialShootingA atTop (nhds 0) := by
  have hs : Tendsto (fun n : ℕ => n+radialInnerShootingThreshold) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_add_right n _) tendsto_id
  have hh := ((tendsto_one_div_atTop_nhds_zero_nat :
    Tendsto (fun n : ℕ => 1/(n : ℝ)) atTop (nhds 0)).comp hs).div_const 2
  have he : radialShootingA=(fun n : ℕ => (1/((n+radialInnerShootingThreshold : ℕ) : ℝ))/2) := by
    funext n
    unfold radialShootingA
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [he]
  simpa only [Function.comp_def,zero_div] using hh

theorem radialMatched_pressure_form_small (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ z : ProfileMatchingBall,
      HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
        (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius) →
      radialMatchingMap n z=0 → ∀ r : ℝ, 0 ≤ r →
        r^2*(radialVelocity (6-2*radialShootingA n)
          (fun t => ‖radialMatchedProfile n z t‖) r*
          deriv (fun t => ‖radialMatchedProfile n z t‖^(2*(n+radialInnerShootingThreshold))/
            radialShootingA n) r) ≤
        ε*(r^2*(‖radialMatchedProfile n z r‖^(2*(n+radialInnerShootingThreshold))/
          radialShootingA n)+1) := by
  have ht : ∀ᶠ n in atTop, 1600*radialShootingA n < ε := by
    have h : Tendsto (fun n => 1600*radialShootingA n) atTop (nhds 0) := by
      simpa only [mul_zero] using radialShootingA_tendsto_zero.const_mul 1600
    exact h.eventually (gt_mem_nhds hε)
  filter_upwards [ht,radialMatched_exterior_pressure_transport_small ε hε]
    with n hn he z hX hz r hr
  let V : ℝ → ℝ := fun t =>
    ‖radialMatchedProfile n z t‖^(2*(n+radialInnerShootingThreshold))/radialShootingA n
  let w := radialVelocity (6-2*radialShootingA n) (fun t => ‖radialMatchedProfile n z t‖)
  have ha := (radialShootingA_bounds n (profileMatchingParameter z)).1
  have hV : 0 ≤ V r := div_nonneg (by positivity) ha.le
  change r^2*(w r*deriv V r) ≤ ε*(r^2*V r+1)
  by_cases hi : r ≤ innerBoundaryRadius
  · have hh := radialMatchedInnerPressure_transport n z hX hz r ⟨hr,hi⟩
    have hp : ‖radialMatchedProfile n z r‖^(2*(n+radialInnerShootingThreshold))=
        radialShootingA n*V r := by
      dsimp [V]
      field_simp
    change w r*deriv V r ≤ 1600*‖radialMatchedProfile n z r‖^(2*(n+radialInnerShootingThreshold)) at hh
    rw [hp] at hh
    have hh' := mul_le_mul_of_nonneg_left hh (sq_nonneg r)
    have hc := mul_le_mul_of_nonneg_right hn.le (mul_nonneg (sq_nonneg r) hV)
    nlinarith
  · have hh := he z hX hz r (lt_of_not_ge hi)
    change r^2*|w r*deriv V r| < ε at hh
    have habs := mul_le_mul_of_nonneg_left (le_abs_self (w r*deriv V r)) (sq_nonneg r)
    have hp := mul_nonneg (sq_nonneg r) hV
    nlinarith

end DefocusingNLS

end OAI
