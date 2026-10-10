import OAI.NumberTheory.CubicMoment.Theta.CubicThetaProjectedRadialPoles
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaAngularGammaEquation

namespace OAI

/-! Actual radial Dirichlet continuation and its functional equation.
The selected pole coefficient is computed from the actual cusp constant. -/
noncomputable section
open Filter
open scoped MatrixGroups Topology
namespace CubicFirstMoment

def cubicThetaSelectedRadialDirichlet (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (s : ℂ) : ℂ :=
  cubicThetaAngularUncompletion (g 1 0) 0 s*cubicThetaSelectedRadialCompleted g hc (2*s-1)

def cubicThetaProjectedRadialDirichlet (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (s : ℂ) : ℂ :=
  cubicThetaAngularUncompletion (g 1 0) 0 s*cubicThetaProjectedRadialCompleted g hc (2*s-1)

lemma cubicThetaSelectedRadialDirichlet_meromorphic (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (s : ℂ) :
    MeromorphicAt (cubicThetaSelectedRadialDirichlet g hc) s := by
  have hu := ((cubicThetaAngularUncompletion_entire hc 0).analyticAt s).meromorphicAt
  have ha : Differentiable ℂ (fun z : ℂ => 2*z-1) := by fun_prop
  have hb : Differentiable ℂ (fun z : ℂ => -(2*z-1)) := ha.neg
  have hf := (((cubicThetaSelectedRadialTail_entire g hc).comp ha).analyticAt s).meromorphicAt
  have hg := (((cubicThetaProjectedRadialTail_entire g hc).comp hb).analyticAt s).meromorphicAt
  have hz : MeromorphicAt (fun z : ℂ => 2*z-1) s := (ha.analyticAt s).meromorphicAt
  have hp := (MeromorphicAt.const (cubicThetaProjectedRadialConstant g hc) s).div
    (hz.sub (MeromorphicAt.const (2/3:ℂ) s))
  exact hu.mul ((hf.add hg).add hp)

lemma cubicThetaProjectedRadialDirichlet_meromorphic (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (s : ℂ) :
    MeromorphicAt (cubicThetaProjectedRadialDirichlet g hc) s := by
  have hu := ((cubicThetaAngularUncompletion_entire hc 0).analyticAt s).meromorphicAt
  have ha : Differentiable ℂ (fun z : ℂ => 2*z-1) := by fun_prop
  have hb : Differentiable ℂ (fun z : ℂ => -(2*z-1)) := ha.neg
  have hf := (((cubicThetaProjectedRadialTail_entire g hc).comp ha).analyticAt s).meromorphicAt
  have hg := (((cubicThetaSelectedRadialTail_entire g hc).comp hb).analyticAt s).meromorphicAt
  have hz : MeromorphicAt (fun z : ℂ => 2*z-1) s := (ha.analyticAt s).meromorphicAt
  have hp := (MeromorphicAt.const (cubicThetaProjectedRadialConstant g hc) s).div
    (hz.add (MeromorphicAt.const (2/3:ℂ) s))
  exact hu.mul ((hf.add hg).sub hp)

lemma cubicThetaSelectedRadialDirichlet_initial (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) {s : ℂ} (hs : 3/2<s.re) :
    cubicThetaSelectedRadialDirichlet g hc s=
      cubicThetaDirichlet (cubicThetaCoefficientTwist cubicThetaSelectedCoefficient
        (cubicThetaPrimaryCuspCenter g)) (2*s-1) := by
  obtain ⟨h₁,h₂⟩ := cubicThetaAngular_initial_gamma hs 0
  rw [cubicThetaSelectedRadialDirichlet,cubicThetaSelectedRadialCompleted_initial g hc hs,
    ←mul_assoc,mul_comm (cubicThetaAngularUncompletion (g 1 0) 0 s),
    cubicThetaAngular_completion_cancel hc 0 s h₁ h₂,one_mul]

lemma cubicThetaProjectedRadialDirichlet_initial (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) {s : ℂ} (hs : 3/2<s.re) :
    cubicThetaProjectedRadialDirichlet g hc s=
      cubicThetaDirichlet (cubicThetaCoefficientTwist (cubicThetaProjectedCoefficient g hc)
        (cubicThetaPrimaryDualCenter g)) (2*s-1) := by
  obtain ⟨h₁,h₂⟩ := cubicThetaAngular_initial_gamma hs 0
  rw [cubicThetaProjectedRadialDirichlet,cubicThetaProjectedRadialCompleted_initial g hc hs,
    ←mul_assoc,mul_comm (cubicThetaAngularUncompletion (g 1 0) 0 s),
    cubicThetaAngular_completion_cancel hc 0 s h₁ h₂,one_mul]

lemma cubicThetaProjectedRadialDirichlet_complete (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) {s : ℂ}
    (h₁ : Complex.Gamma (s+(0:ℕ)/2+1/6)≠0)
    (h₂ : Complex.Gamma (s+(0:ℕ)/2-1/6)≠0) :
    cubicThetaProjectedRadialCompleted g hc (2*s-1)=
      cubicThetaAngularCompletion (g 1 0) 0 s*cubicThetaProjectedRadialDirichlet g hc s := by
  rw [cubicThetaProjectedRadialDirichlet,←mul_assoc,
    cubicThetaAngular_completion_cancel hc 0 s h₁ h₂,one_mul]

lemma cubicThetaSelectedRadialDirichlet_functional (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) {s : ℂ} (hs : s.re<5/6) :
    cubicThetaSelectedRadialDirichlet g hc s=
      (cubicThetaLevelScale (g 1 0):ℂ)^(4*s-2)*((2*Real.pi:ℝ):ℂ)^(4*s-2)*
        metaplecticGammaQuotient 0 s*cubicThetaProjectedRadialDirichlet g hc (1-s) := by
  have h₁ : Complex.Gamma (1-s+(0:ℕ)/2+1/6)≠0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    simp only [Nat.cast_zero,zero_div,add_zero,Complex.add_re,Complex.sub_re,
      Complex.one_re,Complex.div_ofNat_re]
    norm_num
    linarith
  have h₂ : Complex.Gamma (1-s+(0:ℕ)/2-1/6)≠0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    simp only [Nat.cast_zero,zero_div,add_zero,Complex.sub_re,Complex.one_re,Complex.div_ofNat_re]
    norm_num
    linarith
  rw [cubicThetaSelectedRadialDirichlet,cubicThetaSelectedRadialCompleted_functional,
    show -(2*s-1)=2*(1-s)-1 by ring,
    cubicThetaProjectedRadialDirichlet_complete g hc h₁ h₂,←mul_assoc]
  have hr := cubicThetaAngular_archimedean_ratio hc false 0 s
  simpa only [cubicThetaCircleOrder,Bool.false_eq_true,ite_false,Nat.cast_zero] using
    congrArg (fun z : ℂ => z*cubicThetaProjectedRadialDirichlet g hc (1-s)) hr

private lemma radial_affine_punctured :
    Tendsto (fun s : ℂ => 2*s-1) (𝓝[≠] (5/6:ℂ)) (𝓝[≠] (2/3:ℂ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hc : ContinuousAt (fun s : ℂ => 2*s-1) (5/6:ℂ) := by fun_prop
    convert hc.tendsto.mono_left nhdsWithin_le_nhds using 1; norm_num
  · filter_upwards [self_mem_nhdsWithin] with s hs
    change 2*s-1≠(2/3:ℂ)
    intro he
    change s≠(5/6:ℂ) at hs
    apply hs
    linear_combination (1/2:ℂ)*he

lemma cubicThetaSelectedRadialDirichlet_residue (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) :
    Tendsto (fun s : ℂ => (s-5/6)*cubicThetaSelectedRadialDirichlet g hc s)
      (𝓝[≠] (5/6:ℂ))
      (𝓝 (cubicThetaAngularUncompletion (g 1 0) 0 (5/6)*
        cubicThetaProjectedRadialConstant g hc/2)) := by
  have hp := (cubicThetaSelectedRadialCompleted_residue g hc).comp radial_affine_punctured
  have hu := ((cubicThetaAngularUncompletion_entire hc 0).continuous.continuousAt
    (x:=(5/6:ℂ))).tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (5/6:ℂ)≤𝓝 (5/6:ℂ))
  have he := (hu.mul hp).div_const (2:ℂ)
  apply he.congr'
  filter_upwards with s
  unfold cubicThetaSelectedRadialDirichlet
  dsimp only [Function.comp_apply]
  ring

end CubicFirstMoment

end

end OAI
