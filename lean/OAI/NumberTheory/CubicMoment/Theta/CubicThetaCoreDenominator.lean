import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCoreSections
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaSectionDifferential

namespace OAI

/-! A finite sum of squared genuine core bumps is smooth upstairs
and bounded below by one on the arithmetic compact core. -/
noncomputable section
open Set
open scoped ContDiff BigOperators MatrixGroups
namespace CubicFirstMoment

def cubicThetaCoreDenominator (A : Finset CubicThetaQuotient) (q : CubicThetaQuotient) : ℝ :=
  ∑ c∈A, (cubicThetaCoreBump c q)^2

def cubicThetaCoreDenominatorFunction (A : Finset CubicThetaQuotient) (y : ℂ × ℝ) : ℝ :=
  ∑ c∈A, ((cubicThetaSectionFunction (cubicThetaCoreSection c) y).re^2+
    (cubicThetaSectionFunction (cubicThetaCoreSection c) y).im^2)

lemma cubicThetaCoreDenominator_continuous (A : Finset CubicThetaQuotient) :
    Continuous (cubicThetaCoreDenominator A) := by
  apply continuous_finsetSum
  intro c hc
  exact (cubicThetaCoreBump c).continuous.pow 2

lemma cubicThetaCoreDenominator_nonneg (A : Finset CubicThetaQuotient) (q : CubicThetaQuotient) :
    0≤cubicThetaCoreDenominator A q := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

lemma cubicThetaCoreDenominatorFunction_contDiff (A : Finset CubicThetaQuotient) :
    ContDiffOn ℝ ∞ (cubicThetaCoreDenominatorFunction A) {y : ℂ × ℝ | 0<y.2} := by
  apply ContDiffOn.sum
  intro c hc
  have h := (cubicThetaCoreSection c).property.1
  exact (Complex.reCLM.contDiff.comp_contDiffOn h).pow 2 |>.add
    ((Complex.imCLM.contDiff.comp_contDiffOn h).pow 2)

lemma cubicThetaCoreDenominatorFunction_apply (A : Finset CubicThetaQuotient) (p : CubicThetaPoint) :
    cubicThetaCoreDenominatorFunction A p.val=cubicThetaCoreDenominator A (cubicThetaQuotientMap p) := by
  apply Finset.sum_congr rfl
  intro c hc
  rw [cubicThetaSectionFunction_apply _ p.property]
  have he := cubicThetaSectionNorm_apply (cubicThetaCoreSection c) p
  rw [cubicThetaCoreSection_norm] at he
  change ((cubicThetaCoreSection c).val.val p).re^2+
    ((cubicThetaCoreSection c).val.val p).im^2=(cubicThetaCoreBump c (cubicThetaQuotientMap p))^2
  rw [he,← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply,pow_two]

lemma cubicThetaCoreDenominator_covers (S : Finset SL(2,Eisenstein)) (V : ℝ) :
    ∃ A : Finset CubicThetaQuotient, ∀ q∈cubicThetaQuotientCore S V,
      1≤cubicThetaCoreDenominator A q := cubicThetaCoreBump_sum_sq S V

end CubicFirstMoment

end

end OAI
