import OAI.NumberTheory.CubicMoment.Theta.CubicThetaProjectedRadial
import Mathlib.Analysis.Meromorphic.Basic

namespace OAI

/-! The actual primary-projected radial continuation has one pole in
each half-plane. Its residue retains the genuine arithmetic scalar. -/
noncomputable section
open Filter
open scoped Topology MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaSelectedRadialTail_entire (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) :
    Differentiable ℂ (mellin (thetaUpper (cubicThetaSelectedRadialAxis g))) :=
  cubicThetaBoundedScaledUpper_entire (by norm_num : (0:ℝ)≤81)
    cubicThetaSelectedCoefficient_arithmetic_bound 0 _ (cubicThetaLevelScale_pos hc)

lemma cubicThetaProjectedRadialTail_entire (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) :
    Differentiable ℂ (mellin (thetaUpper (cubicThetaProjectedRadialAxis g hc))) :=
  cubicThetaBoundedScaledUpper_entire (by norm_num : (0:ℝ)≤243)
    (cubicThetaProjectedCoefficient_arithmetic_bound g hc) 0 _ (cubicThetaLevelScale_pos hc)

lemma cubicThetaSelectedRadialCompleted_meromorphic (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (s : ℂ) :
    MeromorphicAt (cubicThetaSelectedRadialCompleted g hc) s := by
  have hf := ((cubicThetaSelectedRadialTail_entire g hc).analyticAt s).meromorphicAt
  have hg := (((cubicThetaProjectedRadialTail_entire g hc).comp differentiable_id.neg).analyticAt s).meromorphicAt
  exact (hf.add hg).add ((MeromorphicAt.const _ s).div
    ((MeromorphicAt.id s).sub (MeromorphicAt.const (2/3:ℂ) s)))

lemma cubicThetaProjectedRadialCompleted_meromorphic (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (s : ℂ) :
    MeromorphicAt (cubicThetaProjectedRadialCompleted g hc) s := by
  have hf := ((cubicThetaProjectedRadialTail_entire g hc).analyticAt s).meromorphicAt
  have hg := (((cubicThetaSelectedRadialTail_entire g hc).comp differentiable_id.neg).analyticAt s).meromorphicAt
  exact (hf.add hg).sub ((MeromorphicAt.const _ s).div
    ((MeromorphicAt.id s).add (MeromorphicAt.const (2/3:ℂ) s)))

private lemma radial_pole_limit {f : ℂ→ℂ} {p : ℂ}
    (hf : ContinuousAt f p) (a : ℂ) :
    Tendsto (fun s => (s-p)*(f s+a/(s-p))) (𝓝[≠] p) (𝓝 a) := by
  have hz : Tendsto (fun s : ℂ => s-p) (𝓝 p) (𝓝 (0:ℂ)) := by
    have h : ContinuousAt (fun s : ℂ => s-p) p := continuousAt_id.sub continuousAt_const
    simpa only [sub_self] using h.tendsto
  have he := ((hz.mul hf.tendsto).add_const a).mono_left
    (nhdsWithin_le_nhds : 𝓝[≠] p≤𝓝 p)
  simp only [zero_mul,zero_add] at he
  apply he.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hsp : s-p≠0 := sub_ne_zero.mpr hs
  field_simp

lemma cubicThetaSelectedRadialCompleted_residue (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) :
    Tendsto (fun s : ℂ => (s-2/3)*cubicThetaSelectedRadialCompleted g hc s)
      (𝓝[≠] (2/3:ℂ)) (𝓝 (cubicThetaProjectedRadialConstant g hc)) := by
  exact radial_pole_limit
    ((cubicThetaSelectedRadialTail_entire g hc).continuous.continuousAt.add
      (((cubicThetaProjectedRadialTail_entire g hc).comp differentiable_id.neg).continuous.continuousAt)) _

lemma cubicThetaProjectedRadialCompleted_residue (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) :
    Tendsto (fun s : ℂ => (s+2/3)*cubicThetaProjectedRadialCompleted g hc s)
      (𝓝[≠] (-(2/3):ℂ)) (𝓝 (-cubicThetaProjectedRadialConstant g hc)) := by
  have he := radial_pole_limit (p:=(-(2/3):ℂ))
    ((cubicThetaProjectedRadialTail_entire g hc).continuous.continuousAt.add
      (((cubicThetaSelectedRadialTail_entire g hc).comp differentiable_id.neg).continuous.continuousAt))
    (-cubicThetaProjectedRadialConstant g hc)
  simpa only [sub_neg_eq_add,neg_div,sub_eq_add_neg,neg_neg,cubicThetaProjectedRadialCompleted,Pi.add_apply,
    Function.comp_apply,Pi.neg_apply,id_eq] using he

lemma cubicThetaSelectedRadialCompleted_initial (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) {s : ℂ} (hs : 3/2<s.re) :
    cubicThetaSelectedRadialCompleted g hc (2*s-1)=
      cubicThetaAngularCompletion (g 1 0) 0 s*
        cubicThetaDirichlet (cubicThetaCoefficientTwist cubicThetaSelectedCoefficient
          (cubicThetaPrimaryCuspCenter g)) (2*s-1) := by
  have ht : 2/3<(2*s-1).re := by simp only [Complex.sub_re,Complex.mul_re]; norm_num; linarith
  rw [←(cubicThetaSelectedRadial_mellin g hc ht).2]
  have he := cubicThetaBoundedScaledAxis_mellin (by norm_num : (0:ℝ)≤81)
    cubicThetaSelectedCoefficient_norm (cubicThetaLevelScale_pos hc)
    (cubicThetaPrimaryCuspCenter g) 0 hs
  simp only [cubicThetaSelectedRadialAxis,cubicThetaAngularCompletion,Int.natAbs_zero,
    Nat.cast_zero,zero_div,add_zero,theta_zero,one_mul] at he ⊢
  rw [show -2*s= -(2*s) by ring] at he
  rw [he]
  ring

lemma cubicThetaProjectedRadialCompleted_initial (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) {s : ℂ} (hs : 3/2<s.re) :
    cubicThetaProjectedRadialCompleted g hc (2*s-1)=
      cubicThetaAngularCompletion (g 1 0) 0 s*
        cubicThetaDirichlet (cubicThetaCoefficientTwist (cubicThetaProjectedCoefficient g hc)
          (cubicThetaPrimaryDualCenter g)) (2*s-1) := by
  have ht : 2/3<(2*s-1).re := by simp only [Complex.sub_re,Complex.mul_re]; norm_num; linarith
  rw [←(cubicThetaProjectedRadial_mellin g hc ht).2]
  have he := cubicThetaBoundedScaledAxis_mellin (by norm_num : (0:ℝ)≤243)
    (cubicThetaProjectedCoefficient_bound g hc) (cubicThetaLevelScale_pos hc)
    (cubicThetaPrimaryDualCenter g) 0 hs
  simp only [cubicThetaProjectedRadialAxis,cubicThetaAngularCompletion,Int.natAbs_zero,
    Nat.cast_zero,zero_div,add_zero,theta_zero,one_mul] at he ⊢
  rw [show -2*s= -(2*s) by ring] at he
  rw [he]
  ring

end CubicFirstMoment

end

end OAI
