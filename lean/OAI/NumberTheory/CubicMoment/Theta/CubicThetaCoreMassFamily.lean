import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCoreMassCompact
import Mathlib.Analysis.InnerProductSpace.l2Space

namespace OAI

/-! A finite family of actual core cutoffs is a compact Hilbert-valued
operator; its norm is the sum of the individual squared L2 norms. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

abbrev CubicThetaCoreValueFamily (A : Finset CubicThetaQuotient) :=
  lp (fun _ : A => CubicThetaGlobalL2) 2

def cubicThetaCoreMassFamily (A : Finset CubicThetaQuotient) :
    cubicThetaGlobalEnergySpace →L[ℂ] CubicThetaCoreValueFamily A := by
  classical
  exact ∑ i : A, (lp.singleContinuousLinearMap ℂ (fun _ : A => CubicThetaGlobalL2) 2 i).comp
    (cubicThetaCoreMass i.val)

lemma cubicThetaCoreMassFamily_apply (A : Finset CubicThetaQuotient)
    (u : cubicThetaGlobalEnergySpace) (i : A) :
    cubicThetaCoreMassFamily A u i=cubicThetaCoreMass i.val u := by
  classical
  simp only [cubicThetaCoreMassFamily,sum_apply,ContinuousLinearMap.comp_apply]
  rw [lp.coeFn_sum]
  simp only [Finset.sum_apply,lp.singleContinuousLinearMap_apply,lp.single_apply]
  simp

theorem cubicThetaCoreMassFamily_compact (A : Finset CubicThetaQuotient) :
    IsCompactOperator (cubicThetaCoreMassFamily A) := by
  classical
  apply (compactOperator (RingHom.id ℂ) _ _).sum_mem
  intro i _
  exact (cubicThetaCoreMass_compact i.val).clm_comp
    (lp.singleContinuousLinearMap ℂ (fun _ : A => CubicThetaGlobalL2) 2 i)

lemma cubicThetaCoreMassFamily_norm_sq (A : Finset CubicThetaQuotient)
    (u : cubicThetaGlobalEnergySpace) :
    ‖cubicThetaCoreMassFamily A u‖^2=∑ i : A, ‖cubicThetaCoreMass i.val u‖^2 := by
  have h := lp.norm_rpow_eq_tsum (p:=2) (by norm_num) (cubicThetaCoreMassFamily A u)
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,tsum_fintype,cubicThetaCoreMassFamily_apply] using h

end CubicFirstMoment

end

end OAI
