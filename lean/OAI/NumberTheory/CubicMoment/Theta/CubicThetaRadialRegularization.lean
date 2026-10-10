import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialDirichlet
import Mathlib.Analysis.Complex.RemovableSingularity

namespace OAI

/-! Explicit removal of the actual radial pole. The residue is retained
as the computed cusp constant; no normalization of that constant is assumed. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

def cubicThetaSelectedRadialTail (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (s : ℂ) : ℂ :=
  mellin (thetaUpper (cubicThetaSelectedRadialAxis g)) (2*s-1)+
    mellin (thetaUpper (cubicThetaProjectedRadialAxis g hc)) (-(2*s-1))

lemma cubicThetaSelectedRadialTail_differentiable (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) : Differentiable ℂ (cubicThetaSelectedRadialTail g hc) := by
  have ha : Differentiable ℂ (fun s : ℂ => 2*s-1) := by fun_prop
  exact ((cubicThetaSelectedRadialTail_entire g hc).comp ha).add
    ((cubicThetaProjectedRadialTail_entire g hc).comp ha.neg)

def cubicThetaSelectedRadialResidue (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) : ℂ :=
  cubicThetaAngularUncompletion (g 1 0) 0 (5/6)*cubicThetaProjectedRadialConstant g hc/2

def cubicThetaSelectedRadialRegularized (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (s : ℂ) : ℂ :=
  cubicThetaAngularUncompletion (g 1 0) 0 s*
    ((s-5/6)*cubicThetaSelectedRadialTail g hc s+cubicThetaProjectedRadialConstant g hc/2)

lemma cubicThetaSelectedRadialRegularized_differentiable (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) : Differentiable ℂ (cubicThetaSelectedRadialRegularized g hc) := by
  apply (cubicThetaAngularUncompletion_entire hc 0).mul
  exact ((differentiable_id.sub_const _).mul
    (cubicThetaSelectedRadialTail_differentiable g hc)).add_const _

lemma cubicThetaSelectedRadialRegularized_eq (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) {s : ℂ} (hs : s≠5/6) :
    cubicThetaSelectedRadialRegularized g hc s=
      (s-5/6)*cubicThetaSelectedRadialDirichlet g hc s := by
  have hp : s-5/6≠0 := sub_ne_zero.mpr hs
  have hq : 2*s-1-2/3=2*(s-5/6) := by ring
  unfold cubicThetaSelectedRadialRegularized cubicThetaSelectedRadialDirichlet
    cubicThetaSelectedRadialCompleted cubicThetaSelectedRadialTail
  rw [hq]
  generalize hd : s-(5/6:ℂ)=d at hp ⊢
  field_simp [hp]

@[simp] lemma cubicThetaSelectedRadialRegularized_at_pole (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) :
    cubicThetaSelectedRadialRegularized g hc (5/6)=cubicThetaSelectedRadialResidue g hc := by
  simp only [cubicThetaSelectedRadialRegularized,sub_self,zero_mul,zero_add,
    cubicThetaSelectedRadialResidue]
  ring

def cubicThetaSelectedRadialHolomorphicPart (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (s : ℂ) : ℂ :=
  cubicThetaAngularUncompletion (g 1 0) 0 s*cubicThetaSelectedRadialTail g hc s+
    (cubicThetaProjectedRadialConstant g hc/2)*
      dslope (cubicThetaAngularUncompletion (g 1 0) 0) (5/6) s

lemma cubicThetaSelectedRadialHolomorphicPart_differentiable (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) : Differentiable ℂ (cubicThetaSelectedRadialHolomorphicPart g hc) := by
  have hu := cubicThetaAngularUncompletion_entire hc 0
  have hd : Differentiable ℂ (dslope (cubicThetaAngularUncompletion (g 1 0) 0) (5/6)) := by
    rw [←differentiableOn_univ]
    exact (Complex.differentiableOn_dslope Filter.univ_mem).mpr hu.differentiableOn
  exact (hu.mul (cubicThetaSelectedRadialTail_differentiable g hc)).add (hd.const_mul _)

lemma cubicThetaSelectedRadialDirichlet_pole_decomposition (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) {s : ℂ} (hs : s≠5/6) :
    cubicThetaSelectedRadialDirichlet g hc s=
      cubicThetaSelectedRadialHolomorphicPart g hc s+
        cubicThetaSelectedRadialResidue g hc/(s-5/6) := by
  have hp : s-5/6≠0 := sub_ne_zero.mpr hs
  have hq : 2*s-1-2/3=2*(s-5/6) := by ring
  unfold cubicThetaSelectedRadialDirichlet cubicThetaSelectedRadialCompleted
    cubicThetaSelectedRadialHolomorphicPart cubicThetaSelectedRadialResidue
    cubicThetaSelectedRadialTail
  rw [dslope_of_ne _ hs,slope_def_field,hq]
  field_simp [hp]
  ring

end CubicFirstMoment

end

end OAI
