import OAI.NumberTheory.CubicMoment.Theta.CubicThetaProjectedDirichlet
import OAI.NumberTheory.CubicMoment.Estimates.ThetaMellinCubicPoles

namespace OAI

/-! The zero angular mode of the actual primary projection, with its
constant-to-Fourier ratio retained in the pole coefficient. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaBoundedScaledAxis_zero (a : Eisenstein→ℂ) (z : ℂ) (r t : ℝ) :
    cubicThetaBoundedScaledAxis a 0 z r t=cubicThetaNonconstant a (z,r*t) := by
  rw [cubicThetaBoundedScaledAxis,cubicThetaAngularCoefficient_zero]

def cubicThetaSelectedRadialAxis (g : SL(2,Eisenstein)) : ℝ→ℂ :=
  cubicThetaBoundedScaledAxis cubicThetaSelectedCoefficient 0
    (cubicThetaPrimaryCuspCenter g) (cubicThetaLevelScale (g 1 0))

def cubicThetaProjectedRadialAxis (g : SL(2,Eisenstein)) (hc : primary (g 1 0)) : ℝ→ℂ :=
  cubicThetaBoundedScaledAxis (cubicThetaProjectedCoefficient g hc) 0
    (cubicThetaPrimaryDualCenter g) (cubicThetaLevelScale (g 1 0))

def cubicThetaProjectedRadialConstant (g : SL(2,Eisenstein)) (hc : primary (g 1 0)) : ℂ :=
  cubicThetaProjectedConstant g hc*((cubicThetaLevelScale (g 1 0)^(2/3:ℝ):ℝ):ℂ)

lemma cubicThetaSelectedRadialAxis_reciprocal (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) {t : ℝ} (ht : 0<t) :
    cubicThetaSelectedRadialAxis g t⁻¹=cubicThetaProjectedRadialAxis g hc t+
      cubicThetaProjectedRadialConstant g hc*(t:ℂ)^(2/3:ℂ) := by
  have hr := cubicThetaLevelScale_pos hc
  have hv := mul_pos hr ht
  have h := cubicThetaSelected_projected_plane g hc 0 hv
  have hinv : cubicThetaInversion (g 1 0:ℂ) (0,cubicThetaLevelScale (g 1 0)*t)=
      (0,cubicThetaLevelScale (g 1 0)*t⁻¹) := by
    rw [cubicThetaInversion_center _ hv]
    change (0,(norm (g 1 0)*(cubicThetaLevelScale (g 1 0)*t))⁻¹)=_
    rw [cubicThetaLevelScale_reciprocal hc ht]
  rw [hinv] at h
  simp only [zero_add,cubicThetaProjectedPlane] at h
  rw [Real.mul_rpow hr.le ht.le,Complex.ofReal_mul] at h
  have hp : ((t^(2/3:ℝ):ℝ):ℂ)=(t:ℂ)^(2/3:ℂ) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_ofNat] using Complex.ofReal_cpow ht.le (2/3:ℝ)
  rw [hp] at h
  unfold cubicThetaSelectedRadialAxis cubicThetaProjectedRadialAxis cubicThetaProjectedRadialConstant
  simp only [cubicThetaBoundedScaledAxis_zero]
  rw [h]
  ring

lemma cubicThetaSelectedRadialAxis_small (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) {t : ℝ} (ht : 0<t) :
    cubicThetaSelectedRadialAxis g t=cubicThetaProjectedRadialAxis g hc t⁻¹+
      cubicThetaProjectedRadialConstant g hc*(t:ℂ)^(-(2/3:ℂ)) := by
  have h := cubicThetaSelectedRadialAxis_reciprocal g hc (inv_pos.mpr ht)
  rw [inv_inv,Complex.ofReal_inv,Complex.inv_cpow_ofReal_nonneg ht.le,←Complex.cpow_neg] at h
  exact h

lemma cubicThetaProjectedRadialAxis_small (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) {t : ℝ} (ht : 0<t) :
    cubicThetaProjectedRadialAxis g hc t=cubicThetaSelectedRadialAxis g t⁻¹-
      cubicThetaProjectedRadialConstant g hc*(t:ℂ)^(2/3:ℂ) := by
  have h := cubicThetaSelectedRadialAxis_reciprocal g hc ht
  linear_combination -h

def cubicThetaSelectedRadialCompleted (g : SL(2,Eisenstein)) (hc : primary (g 1 0))
    (s : ℂ) : ℂ :=
  mellin (thetaUpper (cubicThetaSelectedRadialAxis g)) s+
    mellin (thetaUpper (cubicThetaProjectedRadialAxis g hc)) (-s)+
      cubicThetaProjectedRadialConstant g hc/(s-2/3)

def cubicThetaProjectedRadialCompleted (g : SL(2,Eisenstein)) (hc : primary (g 1 0))
    (s : ℂ) : ℂ :=
  mellin (thetaUpper (cubicThetaProjectedRadialAxis g hc)) s+
    mellin (thetaUpper (cubicThetaSelectedRadialAxis g)) (-s)-
      cubicThetaProjectedRadialConstant g hc/(s+2/3)

lemma cubicThetaSelectedRadial_mellin (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) {s : ℂ} (hs : 2/3<s.re) :
    MellinConvergent (cubicThetaSelectedRadialAxis g) s ∧
      mellin (cubicThetaSelectedRadialAxis g) s=cubicThetaSelectedRadialCompleted g hc s := by
  have H := theta_mellin_split_cubic_poles (f:=cubicThetaSelectedRadialAxis g) (g:=cubicThetaProjectedRadialAxis g hc)
    (a:=cubicThetaProjectedRadialConstant g hc) (b:=0)
    (fun t ht => by simpa only [zero_mul,add_zero] using cubicThetaSelectedRadialAxis_small g hc ht)
    hs
    (cubicThetaBoundedScaledUpper_mellinConvergent (by norm_num : (0:ℝ)≤81)
      cubicThetaSelectedCoefficient_arithmetic_bound 0 _ (cubicThetaLevelScale_pos hc) s)
    (cubicThetaBoundedScaledUpper_mellinConvergent (by norm_num : (0:ℝ)≤243)
      (cubicThetaProjectedCoefficient_arithmetic_bound g hc) 0 _ (cubicThetaLevelScale_pos hc) (-s))
  simpa only [zero_div,add_zero,cubicThetaSelectedRadialCompleted] using H

lemma cubicThetaProjectedRadial_mellin (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) {s : ℂ} (hs : 2/3<s.re) :
    MellinConvergent (cubicThetaProjectedRadialAxis g hc) s ∧
      mellin (cubicThetaProjectedRadialAxis g hc) s=cubicThetaProjectedRadialCompleted g hc s := by
  have H := theta_mellin_split_cubic_poles (f:=cubicThetaProjectedRadialAxis g hc) (g:=cubicThetaSelectedRadialAxis g)
    (a:=0) (b:= -cubicThetaProjectedRadialConstant g hc)
    (fun t ht => by simpa only [zero_mul,add_zero,neg_mul,sub_eq_add_neg] using
      cubicThetaProjectedRadialAxis_small g hc ht) hs
    (cubicThetaBoundedScaledUpper_mellinConvergent (by norm_num : (0:ℝ)≤243)
      (cubicThetaProjectedCoefficient_arithmetic_bound g hc) 0 _ (cubicThetaLevelScale_pos hc) s)
    (cubicThetaBoundedScaledUpper_mellinConvergent (by norm_num : (0:ℝ)≤81)
      cubicThetaSelectedCoefficient_arithmetic_bound 0 _ (cubicThetaLevelScale_pos hc) (-s))
  simpa only [zero_div,add_zero,neg_div,sub_eq_add_neg,cubicThetaProjectedRadialCompleted] using H

lemma cubicThetaSelectedRadialCompleted_functional (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (s : ℂ) :
    cubicThetaSelectedRadialCompleted g hc s=cubicThetaProjectedRadialCompleted g hc (-s) := by
  unfold cubicThetaSelectedRadialCompleted cubicThetaProjectedRadialCompleted
  rw [neg_neg,show -s+2/3= -(s-2/3) by ring,div_neg]
  ring

end CubicFirstMoment

end

end OAI
