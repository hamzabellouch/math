import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialInnerShootingLimit
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorShootingFamily
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchingFactorContinuity
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeSlowLogarithm
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialCompactTransform

namespace OAI

/-! The simultaneous nonlinear boundary-value and logarithmic-slope matching map. -/

open Filter
namespace DefocusingNLS
open ProfileCertificate

noncomputable def radialMatchingNu (z : ProfileMatchingBall) (e : ℝ) : ℂ :=
  2*Complex.I*(radialShootingB (profileMatchingParameter z) : ℂ)-(e : ℂ)

noncomputable def radialMatchingTransform (z : ProfileMatchingBall) (e : ℝ)
    (I E : ℂ × ℂ) : ℂ × ℂ :=
  (100*(Complex.exp (radialMatchingNu z e*(Real.log innerBoundaryRadius : ℂ))*E.1-I.1),
    (I.2/I.1-(radialMatchingNu z e*E.1+E.2)/((innerBoundaryRadius : ℂ)*E.1))/
      radialFreeMatchingFactor (profileMatchingParameter z))

noncomputable def radialMatchingMap (n : ℕ) (z : ProfileMatchingBall) : ℂ × ℂ :=
  radialMatchingTransform z (1/((n+radialInnerShootingThreshold : ℕ) : ℝ))
    (radialShootingInnerBoundary n (profileMatchingParameter z))
    (radialShootingExteriorJet (n+radialInnerShootingThreshold) z)

theorem radialMatchingNu_eq (n : ℕ) (z : ProfileMatchingBall) :
    radialMatchingNu z (1/((n+radialInnerShootingThreshold : ℕ) : ℝ))=
      radialShootingNu (n+radialInnerShootingThreshold) z := by
  unfold radialMatchingNu radialShootingNu radialShootingQ
  push_cast
  ring

theorem continuousAt_radialMatchingTransform (z : ProfileMatchingBall) (e : ℝ)
    (I E : ℂ × ℂ) (hI : I.1 ≠ 0) (hE : E.1 ≠ 0) :
    ContinuousAt
      (fun t : ProfileMatchingBall × ℝ × (ℂ × ℂ) × (ℂ × ℂ) =>
        radialMatchingTransform t.1 t.2.1 t.2.2.1 t.2.2.2) (z,e,I,E) := by
  have hν : Continuous (fun t : ProfileMatchingBall × ℝ × (ℂ × ℂ) × (ℂ × ℂ) =>
      radialMatchingNu t.1 t.2.1) := by
    unfold radialMatchingNu radialShootingB profileMatchingParameter
    fun_prop
  have hK := continuous_radialFreeMatchingFactor.comp
    (continuous_profileMatchingParameter.comp
      (continuous_fst : Continuous (fun t : ProfileMatchingBall × ℝ × (ℂ × ℂ) × (ℂ × ℂ) => t.1)))
  have hB : (innerBoundaryRadius : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (by linarith [innerBoundaryRadius_bounds.1])
  unfold radialMatchingTransform
  apply ContinuousAt.prodMk
  · fun_prop
  · exact ((continuous_snd.snd.fst.snd.continuousAt.div
      continuous_snd.snd.fst.fst.continuousAt hI).sub
      (((hν.continuousAt.mul continuous_snd.snd.snd.fst.continuousAt).add
        continuous_snd.snd.snd.snd.continuousAt).div
          (continuousAt_const.mul continuous_snd.snd.snd.fst.continuousAt) (mul_ne_zero hB hE))).div
      hK.continuousAt (radialFreeMatchingFactor_ne_zero (profileMatchingParameter z))

theorem radialShootingInnerBoundary_ne_zero (n : ℕ) (w : RadialShootingDisk) :
    (radialShootingInnerBoundary n w).1 ≠ 0 := by
  have hi := (radialShootingInnerAmplitude_spec n w).2.2.2.2.1
    innerBoundaryRadius (by rw [radialShootingInnerData_R]; exact ⟨by
      linarith [innerBoundaryRadius_bounds.1],le_rfl⟩)
  have hp : 0 < radialShootingInnerAmplitude n w innerBoundaryRadius := by
    linarith [(radialShootingInnerData n w).lo_lower,hi.1.1]
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne') (Complex.exp_ne_zero _)

theorem radialShootingFreeJet_ne_zero (z : ProfileMatchingBall) :
    (radialFreeSlowJet (radialShootingQ z) (radialShootingM z)
      (Real.log innerBoundaryRadius)).1 ≠ 0 := by
  intro he
  have h := radialShooting_free_value z
  change Complex.exp _*(radialFreeSlowJet (radialShootingQ z) (radialShootingM z)
    (Real.log innerBoundaryRadius)).1=radialShootingValue z at h
  rw [he,mul_zero] at h
  exact (norm_pos_iff.mp (radialShootingValue_norm z).1) h.symm

theorem continuous_radialShootingFreeJet :
    Continuous (fun z : ProfileMatchingBall =>
      radialFreeSlowJet (radialShootingQ z) (radialShootingM z) (Real.log innerBoundaryRadius)) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  exact (continuousAt_radialFreeSlowJet_parameter _ _ (by simp [radialShootingQ]) _).comp
    (f := fun z => (radialShootingQ z,radialShootingM z)) (x := z)
    (continuous_radialShootingQ.prodMk continuous_radialShootingM).continuousAt

theorem radialMatchingTransform_free (z : ProfileMatchingBall) :
    radialMatchingTransform z 0
      (radialFreeInnerJet (profileMatchingParameter z) innerBoundaryRadius)
      (radialFreeSlowJet (radialShootingQ z) (radialShootingM z)
        (Real.log innerBoundaryRadius))=(z.val.1,diskProfile (profileMatchingParameter z)) := by
  have hν : radialMatchingNu z 0=2*Complex.I*(radialShootingB (profileMatchingParameter z) : ℂ) := by
    simp only [radialMatchingNu,Complex.ofReal_zero,sub_zero]
  have hlog := radialFreeSlow_physical_log (radialShootingB (profileMatchingParameter z))
    innerBoundaryRadius (by linarith [innerBoundaryRadius_bounds.1]) (radialShootingM z)
    (radialShootingFreeJet_ne_zero z)
  apply Prod.ext
  · change 100*(Complex.exp _*_ - _)=z.val.1
    rw [hν]
    simp only [radialFreeSlowJet]
    rw [radialShooting_free_value]
    unfold radialShootingValue
    ring
  · change (_-_)/_=diskProfile _
    rw [hν]
    unfold radialShootingQ
    rw [hlog,radialFreeInner_logarithmic_mismatch]
    exact mul_div_cancel_left₀ _ (radialFreeMatchingFactor_ne_zero _)

end DefocusingNLS

end OAI
