import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialClampedPhase

namespace OAI

/-! The normalized limiting phase is exactly zero throughout the flat core. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem radial_velocity_on_plateau (l : ℝ) (A : ℝ → ℝ)
    (hcore : EqOn A (fun _ => 1) (Icc 0 l)) (r : ℝ) (hr : r ∈ Icc 0 l) :
    radialVelocity 6 A r=r/2 := by
  have hav : radialAverage (fun t => (A t)^2) r=1/12 := by
    rw [radialAverage_congr _ (fun _ => (1 : ℝ)) r hr.1 (by
      intro t ht
      simp only [hcore ⟨ht.1,ht.2.trans hr.2⟩,one_pow]),radialAverage_const]
  dsimp [radialVelocity,radialVelocityRatio]
  rw [hcore hr,hav]
  ring

theorem radial_phase_zero_on_plateau (R l : ℝ) (_hl : 0 ≤ l) (hlR : l ≤ R)
    (A : ℝ → ℝ) (hcore : EqOn A (fun _ => 1) (Icc 0 l))
    (r : ℝ) (hr : r ∈ Icc 0 l) :
    radialPhase 6 (radialClampedAmplitude R A) r=0 := by
  let B := radialClampedAmplitude R A
  have hB (t : ℝ) (ht : t ∈ Icc 0 l) : B t=1 :=
    (radialClampedAmplitude_eq R A t ⟨ht.1,ht.2.trans hlR⟩).trans (hcore ht)
  have hv (t : ℝ) (ht : t ∈ Icc 0 l) : (radialVelocity 6 B t-t/2)/2=0 := by
    have hav : radialAverage (fun u => (B u)^2) t=1/12 := by
      rw [radialAverage_congr _ (fun _ => (1 : ℝ)) t ht.1 (by
        intro u hu
        simp only [hB u ⟨hu.1,hu.2.trans ht.2⟩,one_pow]),radialAverage_const]
    dsimp [radialVelocity,radialVelocityRatio]
    rw [hB t ht,hav]
    ring
  change (∫ t in (0 : ℝ)..r, (radialVelocity 6 B t-t/2)/2)=0
  calc
    _ = ∫ _t in (0 : ℝ)..r, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have htI : t ∈ Icc 0 r := uIcc_of_le hr.1 ▸ ht
      exact hv t ⟨htI.1,htI.2.trans hr.2⟩
    _ = 0 := intervalIntegral.integral_zero

end DefocusingNLS

end OAI
