import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeShootingData
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeModulus
import Mathlib.Analysis.Calculus.LocalExtr.Basic

namespace OAI

/-! Positive deformation of the actual free exterior on the certified parameter disk. -/

open Set Filter
namespace DefocusingNLS

noncomputable def radialFreeVelocity (b r : ℝ) : ℝ :=
  r/2+2*(radialFreeLog b r).im

theorem radialFreeVelocity_hasDerivAt (b r : ℝ) (hr : 0 < r)
    (hn : radialFreeRaw b r ≠ 0) :
    HasDerivAt (radialFreeVelocity b)
      (6-11/r*radialFreeVelocity b r-
        2*radialFreeVelocity b r*(radialFreeLog b r).re) r := by
  have hd := ((radial_riccati_components (radialFreeLog b) b r hr.ne'
    (radial_free_log_riccati b r hr hn)).2).const_mul 2
  have he : (fun t => 2*((radialFreeLog b t).im+t/4))=radialFreeVelocity b := by
    funext t
    dsimp [radialFreeVelocity]
    ring
  rw [he] at hd
  apply hd.congr_deriv
  dsimp [radialFreeVelocity]
  field_simp [hr.ne']
  ring

theorem radialFreeVelocity_deformation (w : RadialShootingDisk) :
    let b := radialShootingB w
    ∀ r, innerBoundaryRadius ≤ r →
      0 < radialFreeVelocity b r ∧ radialFreeVelocity b r/r < (543/1000 : ℝ) ∧
      (27/1000 : ℝ) ≤ deriv (radialFreeVelocity b) r := by
  intro b
  let R := radialShootingR w
  let Z := radialShootingZ w
  let u := fun r => (radialFreeLog b r).re
  let v := fun r => (radialFreeLog b r).im+r/4
  have hg := radialShooting_geometry w
  have hR : (3 : ℝ) ≤ R := hg.2.1
  have hRb : R < innerBoundaryRadius := by
    have hh := hg.2.2.2.2.2.1
    change (1/10000-1/100000000 : ℝ) ≤ innerBoundaryRadius-R at hh
    linarith
  have hZpos : 0 < Z := by
    have hh := (abs_le.mp (ProfileCertificate.disk_coordinates w).2).1
    dsimp [Z,radialShootingZ]
    norm_num [ProfileCertificate.centerZ,ProfileCertificate.radius] at hh ⊢
    linarith
  have hRZ : R^2/4=Z := freeProfileRadius_sq hZpos.le
  have hraw (r : ℝ) (hr : R ≤ r) : radialFreeRaw b r ≠ 0 := by
    apply (ProfileCertificate.disk_free_exterior w (r^2/4) ?_).1
    change Z ≤ r^2/4
    nlinarith
  have hd (r : ℝ) (hr : R ≤ r) :=
    (radial_riccati_components (radialFreeLog b) b r (by linarith)
      (radial_free_log_riccati b r (by linarith) (hraw r hr))).2
  have hvR : 0 ≤ v R := by
    have hj := ProfileCertificate.diskProfile_bound w
    have him := (abs_le.mp (Complex.abs_re_le_norm (ProfileCertificate.freeProfileJ b Z))).1
    have he := (radialFreeLog_components_j b R (by linarith)).2
    rw [hRZ] at he
    change v R=R*((1/4 : ℝ)+(ProfileCertificate.freeProfileJ b Z).re/2) at he
    rw [he]
    have hh : 0 ≤ (1/4 : ℝ)+(ProfileCertificate.freeProfileJ b Z).re/2 := by
      change ‖ProfileCertificate.freeProfileJ b Z‖ < _ at hj
      linarith
    exact mul_nonneg (by linarith) hh
  have hv (r : ℝ) (hr : R ≤ r) : 0 ≤ v r := by
    apply radial_phase_nonneg u v R r
      (fun t ht => (hd t ht.1).continuousAt.continuousWithinAt) hvR
      (fun t ht => hd t ht.1) r ⟨hr,le_rfl⟩
  have hw : radialFreeVelocity b=fun r => 2*v r := by
    funext r
    dsimp [radialFreeVelocity,v]
    ring
  intro r hr
  have hRr : R < r := hRb.trans_le hr
  have hrp : 0 < r := by linarith
  have hvp : 0 < v r := by
    have hn := hv r hRr.le
    by_contra hh
    have hz : v r=0 := le_antisymm (le_of_not_gt hh) hn
    have hmin : IsLocalMin v r := by
      filter_upwards [Ioi_mem_nhds hRr] with t ht
      rw [hz]
      exact hv t ht.le
    have he := hmin.hasDerivAt_eq_zero (hd r hRr.le)
    change -(2*u r+11/r)*v r+3=0 at he
    rw [hz] at he
    norm_num at he
  have hj := (ProfileCertificate.disk_free_exterior w (r^2/4) (by
    change Z ≤ r^2/4
    nlinarith)).2.1
  change (ProfileCertificate.freeProfileJ b (r^2/4)).re < (43/1000 : ℝ) at hj
  have he := (radialFreeLog_components_j b r hrp).2
  change v r=r*((1/4 : ℝ)+(ProfileCertificate.freeProfileJ b (r^2/4)).re/2) at he
  have hvr : v r/r < (543/2000 : ℝ) := by
    rw [he,mul_div_cancel_left₀ _ hrp.ne']
    linarith
  have hu : u r ≤ 0 := radialFreeLog_nonpos_on_disk w r hr
  have huv : u r*v r ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hu hvp.le
  refine ⟨?_,?_,?_⟩
  · rw [hw]
    positivity
  · rw [hw,mul_div_assoc]
    linarith
  · rw [hw,((hd r hRr.le).const_mul 2).deriv]
    have halg : 2*(-(2*u r+11/r)*v r+3)=6-4*(u r*v r)-22*(v r/r) := by ring
    rw [halg]
    linarith

end DefocusingNLS

end OAI
