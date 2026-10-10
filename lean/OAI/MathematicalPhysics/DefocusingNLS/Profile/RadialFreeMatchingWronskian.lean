import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialWronskian
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeShootingData
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeRiccati

namespace OAI

/-! The exact free logarithmic mismatch at the fixed matching radius. -/

open Set MeasureTheory Filter
namespace DefocusingNLS

theorem radialFreeInnerJet_hasDerivAt (w : RadialShootingDisk) (r : ℝ)
    (hr : r ∈ Ioo (radialShootingR w) innerBoundaryRadius) :
    HasDerivAt (fun t => (radialFreeInnerJet w t).1) (radialFreeInnerJet w r).2 r ∧
    HasDerivAt (fun t => (radialFreeInnerJet w t).2)
      (-radialFreeCoefficient r*(radialFreeInnerJet w r).2-
        (radialShootingB w : ℂ)*(radialFreeInnerJet w r).1) r := by
  obtain ⟨hJ,hFI,hGI,_⟩ := radialFreeInnerJet_spec w
  have he : ∀ᶠ t in nhds r, t ∈ Icc (radialShootingR w) innerBoundaryRadius :=
    mem_of_superset (isOpen_Ioo.mem_nhds hr) Ioo_subset_Icc_self
  have hi := (hJ.snd.integral_hasStrictDerivAt (radialShootingR w) r).hasDerivAt
  have hc := (radialFreeField_continuousOn_curve (radialShootingB w)
    (radialShootingR w) innerBoundaryRadius
    (by linarith [(radialShooting_geometry w).2.1]) (radialFreeInnerJet w) hJ).snd
  have hc' := hc.continuousAt (Icc_mem_nhds hr.1 hr.2)
  have hint : IntervalIntegrable (fun t => -radialFreeCoefficient t*(radialFreeInnerJet w t).2-
      (radialShootingB w : ℂ)*(radialFreeInnerJet w t).1) volume (radialShootingR w) r :=
    ContinuousOn.intervalIntegrable_of_Icc hr.1.le
      (hc.mono (fun t ht => ⟨ht.1,ht.2.trans hr.2.le⟩))
  refine ⟨?_,?_⟩
  · exact (hi.const_add 1).congr_of_eventuallyEq (he.mono (fun t ht => hFI t ht))
  · exact (intervalIntegral.integral_hasDerivAt_right hint
      ⟨Icc (radialShootingR w) innerBoundaryRadius,Icc_mem_nhds hr.1 hr.2,
        hc.aestronglyMeasurable measurableSet_Icc⟩ hc').congr_of_eventuallyEq
      (he.mono (fun t ht => hGI t ht))

theorem radialShootingRaw_ne_zero (w : RadialShootingDisk) (r : ℝ)
    (hr : radialShootingR w ≤ r) : radialFreeRaw (radialShootingB w) r ≠ 0 := by
  have hR := (radialShooting_geometry w).2.1
  have hz : 0 ≤ radialShootingZ w := by
    have hh := (ProfileCertificate.disk_coordinates w).2
    dsimp [radialShootingZ]
    norm_num [ProfileCertificate.centerZ,ProfileCertificate.radius] at hh ⊢
    linarith [(abs_le.mp hh).1]
  have he : (radialShootingR w)^2/4=radialShootingZ w := freeProfileRadius_sq hz
  exact (ProfileCertificate.disk_free_exterior w (r^2/4) (by
    change radialShootingZ w ≤ r^2/4
    nlinarith)).1

noncomputable def radialFreeMatchingFactor (w : RadialShootingDisk) : ℂ :=
  -((radialShootingR w)^11 : ℝ)*Complex.exp (Complex.I*((radialShootingR w)^2/4 : ℝ))*
    (Complex.I*(radialShootingR w/2 : ℝ))*radialFreeRaw (radialShootingB w) (radialShootingR w)/
    (((innerBoundaryRadius^11 : ℝ) : ℂ)*Complex.exp (Complex.I*(innerBoundaryRadius^2/4 : ℝ))*
      (radialFreeInnerJet w innerBoundaryRadius).1*radialFreeRaw (radialShootingB w) innerBoundaryRadius)

theorem radialFreeInner_boundary_ne_zero (w : RadialShootingDisk) :
    (radialFreeInnerJet w innerBoundaryRadius).1 ≠ 0 := by
  apply norm_pos_iff.mp
  have h := (radialFreeInnerJet_spec w).2.2.2.2.1
  linarith

theorem radialFreeMatchingFactor_ne_zero (w : RadialShootingDisk) :
    radialFreeMatchingFactor w ≠ 0 := by
  have hR : (radialShootingR w : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (by linarith [(radialShooting_geometry w).2.1])
  have hB : (innerBoundaryRadius : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (by linarith [innerBoundaryRadius_bounds.1])
  have hRawR := radialShootingRaw_ne_zero w (radialShootingR w) le_rfl
  have hRawB := radialShootingRaw_ne_zero w innerBoundaryRadius (radialShooting_geometry w).2.2.2.1
  unfold radialFreeMatchingFactor
  push_cast
  exact div_ne_zero
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ hR))
      (Complex.exp_ne_zero _)) (mul_ne_zero Complex.I_ne_zero (div_ne_zero hR (by norm_num)))) hRawR)
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hB) (Complex.exp_ne_zero _))
      (radialFreeInner_boundary_ne_zero w)) hRawB)

theorem radialFreeInner_logarithmic_mismatch (w : RadialShootingDisk) :
    (radialFreeInnerJet w innerBoundaryRadius).2/(radialFreeInnerJet w innerBoundaryRadius).1-
      radialFreeLog (radialShootingB w) innerBoundaryRadius=
      radialFreeMatchingFactor w*ProfileCertificate.diskProfile w := by
  let R := radialShootingR w
  let B := innerBoundaryRadius
  let F := fun r => (radialFreeInnerJet w r).1
  let D := fun r => (radialFreeInnerJet w r).2
  let G := radialFreeRaw (radialShootingB w)
  have hR : 0 < R := by dsimp [R]; linarith [(radialShooting_geometry w).2.1]
  have hRB : R ≤ B := (radialShooting_geometry w).2.2.2.1
  have hFc : Continuous F := (radialFreeInnerJet_spec w).1.fst
  have hDc : Continuous D := (radialFreeInnerJet_spec w).1.snd
  have hG (r : ℝ) (hr : r ∈ Icc R B) : HasDerivAt G (deriv G r) r :=
    (radialFreeRaw_hasDerivAt (radialShootingB w) r (hR.trans_le hr.1)).differentiableAt.hasDerivAt
  have hD (r : ℝ) (hr : r ∈ Icc R B) :=
    radialFreeRaw_hasDerivAt_deriv (radialShootingB w) r (hR.trans_le hr.1)
  have hc : ContinuousOn (fun t => (t^11 : ℝ)*Complex.exp (Complex.I*(t^2/4 : ℝ))*
      (F t*deriv G t-D t*G t)) (Icc R B) := by
    have hGc : ContinuousOn G (Icc R B) := fun r hr => (hG r hr).continuousAt.continuousWithinAt
    have hDGc : ContinuousOn (deriv G) (Icc R B) := fun r hr => (hD r hr).continuousAt.continuousWithinAt
    exact ((Complex.continuous_ofReal.comp (continuous_id.pow 11)).continuousOn.mul
      (by fun_prop)).mul ((hFc.continuousOn.mul hDGc).sub (hDc.continuousOn.mul hGc))
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hRB hc
    (fun t ht => radial_free_weighted_wronskian_derivative (radialShootingB w) t
      (ne_of_gt (hR.trans ht.1)) F D G (deriv G)
      (radialFreeInnerJet_hasDerivAt w t ht).1 (hG t ⟨ht.1.le,ht.2.le⟩)
      (radialFreeInnerJet_hasDerivAt w t ht).2 (hD t ⟨ht.1.le,ht.2.le⟩))
    (continuous_const.intervalIntegrable R B)
  rw [intervalIntegral.integral_zero] at he
  have hF0 : F R=1 := by simpa [F,R] using (radialFreeInnerJet_spec w).2.1 R ⟨le_rfl,hRB⟩
  have hD0 : D R=0 := by simpa [D,R] using (radialFreeInnerJet_spec w).2.2.1 R ⟨le_rfl,hRB⟩
  have hGR : G R ≠ 0 := radialShootingRaw_ne_zero w R le_rfl
  have hGB : G B ≠ 0 := radialShootingRaw_ne_zero w B hRB
  have hFB : F B ≠ 0 := radialFreeInner_boundary_ne_zero w
  have hZ : 0 ≤ radialShootingZ w := by
    have hh := (ProfileCertificate.disk_coordinates w).2
    dsimp [radialShootingZ]
    norm_num [ProfileCertificate.centerZ,ProfileCertificate.radius] at hh ⊢
    linarith [(abs_le.mp hh).1]
  have hsq : R^2/4=radialShootingZ w := freeProfileRadius_sq hZ
  have hlog := radialFreeLog_eq_j (radialShootingB w) R hR
  rw [hsq] at hlog
  change deriv G R/G R=Complex.I*(R/2 : ℝ)*ProfileCertificate.diskProfile w at hlog
  have hdR := (div_eq_iff hGR).mp hlog
  simp only [hF0,hD0,one_mul,zero_mul,sub_zero] at he
  rw [hdR] at he
  change D B/F B-deriv G B/G B=_
  unfold radialFreeMatchingFactor
  change D B/F B-deriv G B/G B=
    (-((R^11 : ℝ) : ℂ)*Complex.exp (Complex.I*(R^2/4 : ℝ))*(Complex.I*(R/2 : ℝ))*G R/
      (((B^11 : ℝ) : ℂ)*Complex.exp (Complex.I*(B^2/4 : ℝ))*F B*G B))*_
  have hB : ((B^11 : ℝ) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (pow_ne_zero _ (by dsimp [B]; linarith [innerBoundaryRadius_bounds.1]))
  field_simp [hFB,hGB,hB,Complex.exp_ne_zero]
  linear_combination he

end DefocusingNLS

end OAI
