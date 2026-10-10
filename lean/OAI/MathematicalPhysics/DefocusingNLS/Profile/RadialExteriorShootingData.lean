import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialBoundaryCoefficientContinuity
import OAI.MathematicalPhysics.DefocusingNLS.Profile.ProfileProductMatching

namespace OAI

/-! Compact shooting data for simultaneous complex value and slope matching. -/

open Set
namespace DefocusingNLS
open ProfileCertificate

noncomputable def radialShootingValue (z : ProfileMatchingBall) : ℂ :=
  (radialFreeInnerJet (profileMatchingParameter z) innerBoundaryRadius).1+z.val.1/100

noncomputable def radialShootingQ (z : ProfileMatchingBall) : ℂ :=
  -Complex.I*(radialShootingB (profileMatchingParameter z) : ℂ)

noncomputable def radialShootingM (z : ProfileMatchingBall) : ℂ :=
  radialShootingValue z*radialFreePhysicalBoundaryCoefficient
    (radialShootingB (profileMatchingParameter z)) 1

theorem continuous_profileMatchingParameter : Continuous profileMatchingParameter :=
  (continuous_subtype_val.snd).subtype_mk _

theorem continuous_radialShootingValue : Continuous radialShootingValue := by
  exact (continuous_radialFreeInner_boundary.fst.comp continuous_profileMatchingParameter).add
    (continuous_subtype_val.fst.div_const _)

theorem continuous_radialShootingQ : Continuous radialShootingQ := by
  unfold radialShootingQ radialShootingB
  fun_prop

theorem continuous_radialShootingM : Continuous radialShootingM :=
  continuous_radialShootingValue.mul
    (continuous_radialFreePhysical_unitCoefficient.comp continuous_profileMatchingParameter)

theorem radialShootingValue_norm (z : ProfileMatchingBall) :
    0 < ‖radialShootingValue z‖ ∧ ‖radialShootingValue z‖ < 1 := by
  have hz : ‖z.val‖ ≤ (radius : ℝ) := by
    simpa only [Metric.mem_closedBall,dist_zero_right] using z.property
  have hζ : ‖z.val.1/100‖ ≤ (1/10000000000 : ℝ) := by
    rw [norm_div]
    norm_num
    have hh := (norm_fst_le z.val).trans hz
    norm_num [radius] at hh
    linarith
  have hF := (radialFreeInnerJet_spec (profileMatchingParameter z)).2.2.2.2
  have hu := norm_add_le
    (radialFreeInnerJet (profileMatchingParameter z) innerBoundaryRadius).1 (z.val.1/100)
  have hl := norm_sub_norm_le
    (radialFreeInnerJet (profileMatchingParameter z) innerBoundaryRadius).1
    (radialShootingValue z)
  have he : (radialFreeInnerJet (profileMatchingParameter z) innerBoundaryRadius).1-
      radialShootingValue z= -(z.val.1/100) := by unfold radialShootingValue; abel
  rw [he,norm_neg] at hl
  have hu' : ‖radialShootingValue z‖ ≤
      ‖(radialFreeInnerJet (profileMatchingParameter z) innerBoundaryRadius).1‖+‖z.val.1/100‖ := hu
  constructor <;> linarith [hF.1,hF.2]

theorem radialShootingM_ne_zero (z : ProfileMatchingBall) : radialShootingM z ≠ 0 :=
  mul_ne_zero (norm_pos_iff.mp (radialShootingValue_norm z).1)
    (radialFreePhysicalBoundaryCoefficient_spec (profileMatchingParameter z) 1 (by norm_num)).1

theorem radialShooting_free_value (z : ProfileMatchingBall) :
    Complex.exp (2*Complex.I*(radialShootingB (profileMatchingParameter z) : ℂ)*
      (Real.log innerBoundaryRadius : ℂ))*
      radialFreeSlowValue (radialShootingQ z) (radialShootingM z)
        (Real.log innerBoundaryRadius)=radialShootingValue z := by
  have hh := (radialFreePhysicalBoundaryCoefficient_spec (profileMatchingParameter z) 1
    (by norm_num)).2.1
  change Complex.exp (2*Complex.I*(radialShootingB (profileMatchingParameter z) : ℂ)*
    (Real.log innerBoundaryRadius : ℂ))*radialFreeSlowValue (radialShootingQ z)
    (radialFreePhysicalBoundaryCoefficient (radialShootingB (profileMatchingParameter z)) 1) _=
      (1 : ℂ) at hh
  unfold radialShootingM
  rw [radialFreeSlowValue_mul]
  calc
    _ = radialShootingValue z*(Complex.exp _*radialFreeSlowValue (radialShootingQ z)
      (radialFreePhysicalBoundaryCoefficient (radialShootingB (profileMatchingParameter z)) 1)
      (Real.log innerBoundaryRadius)) := by ring
    _ = _ := by rw [hh,mul_one]

theorem radialShooting_free_annulus (z : ProfileMatchingBall) :
    ∃ δ ρ : ℝ, 0 < δ ∧ δ < ‖radialShootingM z‖ ∧ ‖radialShootingM z‖+2*δ < 1 ∧ ρ < 1 ∧
      (∀ t, Real.log innerBoundaryRadius ≤ t →
        ‖(radialFreeSlowJet (radialShootingQ z) (radialShootingM z) t).1‖+2*δ ≤ ρ) ∧
      ∀ t, Real.log innerBoundaryRadius ≤ t →
        δ < ‖(radialFreeSlowJet (radialShootingQ z) (radialShootingM z) t).1‖ := by
  apply radialFreeSlow_annulus (profileMatchingParameter z) (radialShootingM z)
    (radialShootingM_ne_zero z)
  have he := congrArg norm (radialShooting_free_value z)
  have hn : ‖Complex.exp (2*Complex.I*(radialShootingB (profileMatchingParameter z) : ℂ)*
      (Real.log innerBoundaryRadius : ℂ))‖=1 := by
    simp [Complex.norm_exp,Complex.mul_re,Complex.mul_im]
  rw [norm_mul,hn,one_mul] at he
  change ‖radialFreeSlowValue (radialShootingQ z) (radialShootingM z)
    (Real.log innerBoundaryRadius)‖ < 1
  rw [he]
  exact (radialShootingValue_norm z).2

end DefocusingNLS

end OAI
