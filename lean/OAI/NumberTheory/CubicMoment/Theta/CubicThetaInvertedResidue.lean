import OAI.NumberTheory.CubicMoment.Theta.CubicThetaInvertedDirichlet

namespace OAI

/-! The inverted-cusp scalar coefficient has the same residue as the
principal cusp. This assertion concerns scalar scattering coefficients;
it does not identify the nonconstant automorphic residues. -/
noncomputable section
open Filter
open scoped Topology
namespace CubicFirstMoment

def cubicThetaInvertedScatteringFactor (s : ℂ) : ℂ :=
  ((3:ℂ)^(3*s-3)-1)/2

lemma cubicThetaInvertedScatteringFactor_analytic (s : ℂ) :
    AnalyticAt ℂ cubicThetaInvertedScatteringFactor s := by
  let _ : NeZero (3:ℂ) := ⟨by norm_num⟩
  have ha : AnalyticAt ℂ (fun z : ℂ => 3*z-3) s := by fun_prop
  exact (((differentiable_const_cpow_of_neZero (3:ℂ)).analyticAt _).comp ha).sub
    analyticAt_const |>.div analyticAt_const (by norm_num)

lemma cubicThetaInvertedScatteringFactor_pole :
    cubicThetaInvertedScatteringFactor (4/3:ℂ)=1 := by
  norm_num [cubicThetaInvertedScatteringFactor]

theorem cubicThetaInvertedConstantContinuation_factor (s : ℂ) :
    cubicThetaInvertedConstantContinuation s=
      cubicThetaInvertedScatteringFactor s*cubicThetaConstantContinuation s := by
  have hpow : (3:ℂ)^(3*s-3)*(3:ℂ)^(3-3*s)=1 := by
    rw [←Complex.cpow_add _ _ (by norm_num : (3:ℂ)≠0),show 3*s-3+(3-3*s)=0 by ring]
    simp
  unfold cubicThetaInvertedConstantContinuation cubicThetaInvertedScatteringFactor
    cubicThetaConstantContinuation
  symm
  calc
    _ = (((3:ℂ)^(3*s-3)*(3:ℂ)^(3-3*s)-(3:ℂ)^(3-3*s))/
        (1-(3:ℂ)^(2-3*s)))*principalIdealZeta (3*s-3)/principalIdealZeta (3*s-2) := by ring
    _ = _ := by rw [hpow]

def cubicThetaInvertedConstantRegular (s : ℂ) : ℂ :=
  cubicThetaInvertedScatteringFactor s*cubicThetaConstantRegular s

lemma cubicThetaInvertedConstantRegular_analyticAt :
    AnalyticAt ℂ cubicThetaInvertedConstantRegular (4/3:ℂ) :=
  (cubicThetaInvertedScatteringFactor_analytic _).mul cubicThetaConstantRegular_analyticAt

lemma cubicThetaInvertedConstantRegular_eq {s : ℂ}
    (hs0 : 3*s-3≠0) (hs1 : 3*s-3≠1) :
    cubicThetaInvertedConstantRegular s=(s-4/3)*cubicThetaInvertedConstantContinuation s := by
  rw [cubicThetaInvertedConstantRegular,cubicThetaConstantRegular_eq hs0 hs1,
    cubicThetaInvertedConstantContinuation_factor]
  ring

theorem cubicThetaInvertedConstantContinuation_residue :
    Tendsto (fun s : ℂ => (s-4/3)*cubicThetaInvertedConstantContinuation s)
      (𝓝[≠] (4/3:ℂ))
      (𝓝 ((principalThetaConstant/(residueHeckeScale 1:ℂ))/(4*principalIdealZeta 2))) := by
  have hf := ((cubicThetaInvertedScatteringFactor_analytic (4/3:ℂ)).continuousAt.tendsto).mono_left
    (nhdsWithin_le_nhds : 𝓝[≠] (4/3:ℂ)≤𝓝 (4/3:ℂ))
  have ht := hf.mul cubicThetaConstantContinuation_residue
  rw [cubicThetaInvertedScatteringFactor_pole,one_mul] at ht
  apply ht.congr'
  filter_upwards with s
  rw [cubicThetaInvertedConstantContinuation_factor]
  ring

end CubicFirstMoment

end

end OAI
