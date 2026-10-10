import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCoreDenominator
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaC1Division
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaC1Localization

namespace OAI

/-! Exact finite core reconstruction after division by the positive
sum of squared core bumps. -/
noncomputable section
open Set
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicThetaCoreDenominator_pullback (A : Finset CubicThetaQuotient) :
    ContDiffOn ℝ 1 (fun y => cubicThetaCoreDenominator A
      (cubicThetaQuotientMap (cubicThetaPointInclusion.symm y))) {y : ℂ × ℝ | 0<y.2} := by
  apply ((cubicThetaCoreDenominatorFunction_contDiff A).of_le (by simp)).congr
  intro y hy
  have he := cubicThetaCoreDenominatorFunction_apply A (cubicThetaPointInclusion.symm y)
  have hi : (cubicThetaPointInclusion.symm y).val=y :=
    cubicThetaPointInclusion.right_inv (by rwa [cubicThetaPointInclusion_target])
  rw [hi] at he
  exact he.symm

lemma cubicThetaCoreDivision_reconstruction (A : Finset CubicThetaQuotient) (F : CubicThetaSection)
    (hn : ∀ q∈tsupport (cubicThetaSectionNorm F), cubicThetaCoreDenominator A q≠0) :
    let H := cubicThetaSectionDivide F (cubicThetaCoreDenominator A)
      (cubicThetaCoreDenominator_continuous A) hn
    (∑ c∈A, cubicThetaSectionCutoff (cubicThetaCoreSquare c) H)=F := by
  intro H
  ext p
  simp only [AddSubmonoidClass.coe_finsetSum,ContinuousMap.sum_apply]
  change (∑ c∈A, (cubicThetaCoreBump c (cubicThetaQuotientMap p):ℂ)^2*
    (F.val p/(cubicThetaCoreDenominator A (cubicThetaQuotientMap p):ℂ)))=F.val p
  rw [← Finset.sum_mul]
  have hs : (∑ c∈A, (cubicThetaCoreBump c (cubicThetaQuotientMap p):ℂ)^2)=
      (cubicThetaCoreDenominator A (cubicThetaQuotientMap p):ℂ) := by
    simp only [cubicThetaCoreDenominator,Complex.ofReal_sum,Complex.ofReal_pow]
  rw [hs]
  by_cases hf : F.val p=0
  · simp only [hf,zero_div,mul_zero]
  · have hq : cubicThetaQuotientMap p∈tsupport (cubicThetaSectionNorm F) := by
      apply subset_tsupport
      rw [Function.mem_support,cubicThetaSectionNorm_apply]
      exact norm_ne_zero_iff.mpr hf
    have hd : (cubicThetaCoreDenominator A (cubicThetaQuotientMap p):ℂ)≠0 := by
      exact_mod_cast hn _ hq
    field_simp [hd]

end CubicFirstMoment

end

end OAI
