import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeRiccati
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialRiccatiSign
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialBoundaryGeometry

namespace OAI

/-! The certified slow free solution has nonincreasing modulus beyond the matching radius. -/

open Set
namespace DefocusingNLS

theorem radialFreeLog_components_j (b r : ℝ) (hr : 0 < r) :
    (radialFreeLog b r).re = -(r/2)*(ProfileCertificate.freeProfileJ b (r^2/4)).im ∧
    (radialFreeLog b r).im+r/4 =
      r*((1/4 : ℝ)+(ProfileCertificate.freeProfileJ b (r^2/4)).re/2) := by
  rw [radialFreeLog_eq_j b r hr]
  simp only [Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,one_mul,zero_add]
  constructor <;> ring

theorem radialFreeLog_nonpos_on_disk
    (w : Metric.closedBall (0 : ℂ) (ProfileCertificate.radius : ℝ)) :
    let b := (ProfileCertificate.centerB : ℝ)+w.val.re
    ∀ r, innerBoundaryRadius ≤ r → (radialFreeLog b r).re ≤ 0 := by
  intro b
  let Z := (ProfileCertificate.centerZ : ℝ)+w.val.im
  let R := freeProfileRadius Z
  let u := fun r => (radialFreeLog b r).re
  let v := fun r => (radialFreeLog b r).im+r/4
  obtain ⟨hb,hZ⟩ := ProfileCertificate.disk_coordinates w
  have hZ' : |Z-(ProfileCertificate.centerZ : ℝ)| ≤ (1/100000000 : ℝ) := by
    simpa only [Z,add_sub_cancel_left,ProfileCertificate.radius,Rat.cast_div,
      Rat.cast_one,Rat.cast_ofNat] using hZ
  obtain ⟨hR,hS,hshell⟩ := radial_boundary_shell_geometry Z hZ'
  change (3 : ℝ) ≤ R at hR
  change innerBoundaryRadius-R ∈ _ at hshell
  have hRS : R ≤ innerBoundaryRadius := by linarith [hshell.1]
  have hRU : R ≤ (7/2 : ℝ) := by linarith
  have hZ0 : 0 < Z := by
    have hz := (abs_le.mp hZ).1
    dsimp [Z]
    norm_num [ProfileCertificate.centerZ,ProfileCertificate.radius] at hz ⊢
    linarith
  have hb0 : (334/1000 : ℝ) ≤ b := by
    have hb' := (abs_le.mp hb).1
    dsimp [b]
    norm_num [ProfileCertificate.centerB,ProfileCertificate.radius] at hb' ⊢
    linarith
  have hz (r : ℝ) (hr : R ≤ r) : Z ≤ r^2/4 := by
    have hsq := freeProfileRadius_sq hZ0.le
    change R^2/4=Z at hsq
    nlinarith
  have hraw (r : ℝ) (hr : R ≤ r) : radialFreeRaw b r ≠ 0 :=
    (ProfileCertificate.disk_free_exterior w (r^2/4) (hz r hr)).1
  have hd (r : ℝ) (hr : R ≤ r) :=
    radial_riccati_components (radialFreeLog b) b r (by linarith)
      (radial_free_log_riccati b r (by linarith) (hraw r hr))
  have huc : ContinuousOn u (Ici R) := by
    intro r hr
    exact (hd r hr).1.continuousAt.continuousWithinAt
  have hvc : ContinuousOn v (Ici R) := by
    intro r hr
    exact (hd r hr).2.continuousAt.continuousWithinAt
  have hjR : ‖ProfileCertificate.freeProfileJ b Z‖ < (3/1000000000 : ℝ) :=
    ProfileCertificate.diskProfile_bound w
  have hjre := (abs_le.mp (Complex.abs_re_le_norm (ProfileCertificate.freeProfileJ b Z))).1
  have hjim := (abs_le.mp (Complex.abs_im_le_norm (ProfileCertificate.freeProfileJ b Z))).1
  have hjRcomp := radialFreeLog_components_j b R (by linarith)
  rw [show R^2/4=Z from freeProfileRadius_sq hZ0.le] at hjRcomp
  have hvR : 0 ≤ v R := by
    dsimp [v]
    rw [hjRcomp.2]
    have : 0 ≤ (1/4 : ℝ)+(ProfileCertificate.freeProfileJ b Z).re/2 := by linarith
    exact mul_nonneg (by linarith) this
  have huR : u R ≤ (1/100000000 : ℝ) := by
    dsimp [u]
    rw [hjRcomp.1]
    have hRR : R ≤ (10/3 : ℝ) := hRS.trans hS
    nlinarith
  have hvnon : ∀ r ∈ Icc R (7/2 : ℝ), 0 ≤ v r :=
    radial_phase_nonneg u v R (7/2)
      (hvc.mono (fun _ hr => hr.1)) hvR (fun r hr => (hd r hr.1).2)
  have hpot : ∀ r ∈ Icc R (7/2 : ℝ),
      (18/100 : ℝ) < b+r^2/16-(v r)^2 := by
    intro r hr
    have hc := (radialFreeLog_components_j b r (by linarith [hr.1])).2
    have hj := (ProfileCertificate.disk_free_exterior w (r^2/4) (hz r hr.1)).2.1
    have hupper : v r ≤ (543/2000 : ℝ)*r := by
      dsimp [v]
      rw [hc]
      have hh := mul_nonneg (by linarith [hr.1] : 0 ≤ r) (sub_nonneg.mpr hj.le)
      nlinarith
    apply radial_free_potential_lower b r (v r) hb0 (by linarith [hr.1])
      (by nlinarith [hr.1,hr.2]) (hvnon r hr) hupper
  have huS : u innerBoundaryRadius < 0 :=
    radial_riccati_shell u v b R innerBoundaryRadius hR hRS
      (by linarith [hshell.2]) (by linarith [hshell.1])
      (huc.mono (fun _ hr => hr.1)) huR (fun r hr => (hd r hr.1).1)
      (fun r hr => hpot r ⟨hr.1,hr.2.trans (by linarith)⟩)
  have hunon : ∀ r ∈ Icc innerBoundaryRadius (7/2 : ℝ), u r ≤ 0 :=
    radial_riccati_nonpos u v b innerBoundaryRadius (7/2)
      (huc.mono (fun _ hr => hRS.trans hr.1)) huS.le
      (fun r hr => (hd r (hRS.trans hr.1)).1)
      (fun r hr => lt_trans (by norm_num) (hpot r ⟨hRS.trans hr.1,hr.2⟩))
  intro r hr
  by_cases hru : r ≤ (7/2 : ℝ)
  · exact hunon r ⟨hr,hru⟩
  · have hrr : 0 < r := by linarith
    have hj := (ProfileCertificate.disk_free_exterior w (r^2/4)
      (hz r (hRS.trans hr))).2.2 (by nlinarith)
    rw [(radialFreeLog_components_j b r hrr).1]
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hj.le

end DefocusingNLS

end OAI
