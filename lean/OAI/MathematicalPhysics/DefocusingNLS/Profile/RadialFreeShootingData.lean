import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialBoundaryProfile
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialBoundaryContinuity
import OAI.MathematicalPhysics.DefocusingNLS.Profile.ProfileQuotientContinuity

namespace OAI

/-! A continuous boundary jet of the actual free inner IVP on the certified disk. -/

open Set Filter
namespace DefocusingNLS

abbrev RadialShootingDisk := Metric.closedBall (0 : ℂ) (ProfileCertificate.radius : ℝ)

noncomputable def radialShootingB (w : RadialShootingDisk) : ℝ :=
  (ProfileCertificate.centerB : ℝ)+w.val.re

noncomputable def radialShootingZ (w : RadialShootingDisk) : ℝ :=
  (ProfileCertificate.centerZ : ℝ)+w.val.im

noncomputable def radialShootingR (w : RadialShootingDisk) : ℝ :=
  2*Real.sqrt (radialShootingZ w)

theorem radialShooting_geometry (w : RadialShootingDisk) :
    radialShootingB w ∈ Icc (334/1000 : ℝ) (335/1000) ∧
    (3 : ℝ) ≤ radialShootingR w ∧ innerBoundaryRadius ≤ (10/3 : ℝ) ∧
    radialShootingR w ≤ innerBoundaryRadius ∧
    innerBoundaryRadius-radialShootingR w ≤ (1/1000 : ℝ) ∧
    innerBoundaryRadius-radialShootingR w ∈
      Icc (1/10000-1/100000000 : ℝ) (1/10000+1/100000000) := by
  have hb := (ProfileCertificate.disk_coordinates w).1
  have hz := (ProfileCertificate.disk_coordinates w).2
  have hZ : |radialShootingZ w-(ProfileCertificate.centerZ : ℝ)| ≤ (1/100000000 : ℝ) := by
    simpa [radialShootingZ,ProfileCertificate.radius] using hz
  obtain ⟨hR,hu,hwidth⟩ := radial_boundary_shell_geometry (radialShootingZ w) hZ
  have hb' := abs_le.mp hb
  refine ⟨?_,hR,hu,?_,?_,hwidth⟩
  · dsimp [radialShootingB]
    norm_num [ProfileCertificate.centerB,ProfileCertificate.radius] at hb' ⊢
    constructor <;> linarith [hb'.1,hb'.2]
  · change 2*Real.sqrt (radialShootingZ w) ≤ innerBoundaryRadius
    linarith [hwidth.1]
  · change innerBoundaryRadius-2*Real.sqrt (radialShootingZ w) ≤ _
    linarith [hwidth.2]

theorem exists_radialFreeInnerJet (w : RadialShootingDisk) :
    ∃ J : ℝ → ℂ × ℂ, Continuous J ∧
      (∀ r ∈ Icc (radialShootingR w) innerBoundaryRadius,
        (J r).1=1+∫ t in (radialShootingR w)..r, (J t).2) ∧
      (∀ r ∈ Icc (radialShootingR w) innerBoundaryRadius,
        (J r).2=∫ t in (radialShootingR w)..r,
          -radialFreeCoefficient t*(J t).2-(radialShootingB w : ℂ)*(J t).1) ∧
      (∀ r, ‖(J r).1‖ ≤ 2 ∧ ‖(J r).2‖ ≤ 2) ∧
      1-(1/5 : ℝ)*(1/10000)^2 < ‖(J innerBoundaryRadius).1‖ ∧
      ‖(J innerBoundaryRadius).1‖ < 1-(3/20 : ℝ)*(1/10000)^2 := by
  obtain ⟨hb,hl,hu,hlu,hw,hshell⟩ := radialShooting_geometry w
  obtain ⟨F,G,hF,hG,hFI,hGI,hB⟩ := exists_radial_free_components
    (radialShootingB w) (radialShootingR w) innerBoundaryRadius hb hl hu hlu hw
  have he := (radial_free_taylor (radialShootingB w) (radialShootingR w) innerBoundaryRadius
    hb hl hu hlu hw F G hF hG hFI hGI (fun r _ => hB r)
    innerBoundaryRadius ⟨hlu,le_rfl⟩).2
  exact ⟨fun r => (F r,G r),hF.prodMk hG,hFI,hGI,hB,
    radial_free_boundary_gap _ _ _ hb hshell he⟩

noncomputable def radialFreeInnerJet (w : RadialShootingDisk) : ℝ → ℂ × ℂ :=
  Classical.choose (exists_radialFreeInnerJet w)

theorem radialFreeInnerJet_spec (w : RadialShootingDisk) :
    Continuous (radialFreeInnerJet w) ∧
      (∀ r ∈ Icc (radialShootingR w) innerBoundaryRadius,
        (radialFreeInnerJet w r).1=1+∫ t in (radialShootingR w)..r, (radialFreeInnerJet w t).2) ∧
      (∀ r ∈ Icc (radialShootingR w) innerBoundaryRadius,
        (radialFreeInnerJet w r).2=∫ t in (radialShootingR w)..r,
          -radialFreeCoefficient t*(radialFreeInnerJet w t).2-
            (radialShootingB w : ℂ)*(radialFreeInnerJet w t).1) ∧
      (∀ r, ‖(radialFreeInnerJet w r).1‖ ≤ 2 ∧ ‖(radialFreeInnerJet w r).2‖ ≤ 2) ∧
      1-(1/5 : ℝ)*(1/10000)^2 < ‖(radialFreeInnerJet w innerBoundaryRadius).1‖ ∧
      ‖(radialFreeInnerJet w innerBoundaryRadius).1‖ < 1-(3/20 : ℝ)*(1/10000)^2 :=
  Classical.choose_spec (exists_radialFreeInnerJet w)

theorem continuous_radialFreeInner_boundary :
    Continuous (fun w => radialFreeInnerJet w innerBoundaryRadius) := by
  apply SeqContinuous.continuous
  intro w w₀ hw
  have hb : Continuous radialShootingB := by unfold radialShootingB; fun_prop
  have hR : Continuous radialShootingR := by unfold radialShootingR radialShootingZ; fun_prop
  have hg := radialShooting_geometry w₀
  have hgn := fun i => radialShooting_geometry (w i)
  have hs := radialFreeInnerJet_spec w₀
  have hsn := fun i => radialFreeInnerJet_spec (w i)
  exact (radial_free_boundary_tendsto innerBoundaryRadius (radialShootingB w₀) (radialShootingR w₀)
    (fun i => radialShootingB (w i)) (fun i => radialShootingR (w i))
    hg.1 (fun i => (hgn i).1) hg.2.1 (fun i => (hgn i).2.1) hg.2.2.1
    hg.2.2.2.1 (fun i => (hgn i).2.2.2.1) hg.2.2.2.2.1 (fun i => (hgn i).2.2.2.2.1)
    (hb.continuousAt.tendsto.comp hw) (hR.continuousAt.tendsto.comp hw)
    (fun r => (radialFreeInnerJet w₀ r).1) (fun r => (radialFreeInnerJet w₀ r).2)
    (fun i r => (radialFreeInnerJet (w i) r).1) (fun i r => (radialFreeInnerJet (w i) r).2)
    hs.1.fst hs.1.snd (fun i => (hsn i).1.fst) (fun i => (hsn i).1.snd)
    hs.2.1 hs.2.2.1 (fun i => (hsn i).2.1) (fun i => (hsn i).2.2.1)
    (fun r _ => hs.2.2.2.1 r) (fun i r _ => (hsn i).2.2.2.1 r)).1

end DefocusingNLS

end OAI
