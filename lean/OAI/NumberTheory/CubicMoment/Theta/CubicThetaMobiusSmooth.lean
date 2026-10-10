import OAI.NumberTheory.CubicMoment.Theta.CubicThetaMobiusContinuity
import Mathlib.Analysis.Calculus.ContDiff.Operations

namespace OAI

/-! Smoothness of the literal matrix action on positive-height points. -/
noncomputable section
open scoped MatrixGroups ContDiff
namespace CubicFirstMoment

lemma cubicThetaMobiusDenominator_contDiff (g : SL(2,ℂ)) :
    ContDiff ℝ ∞ (cubicThetaMobiusDenominator g) := by
  have hn : ContDiff ℝ ∞ Complex.normSq := by
    change ContDiff ℝ ∞ (fun z : ℂ => Complex.reCLM z*Complex.reCLM z+
      Complex.imCLM z*Complex.imCLM z)
    exact (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
      (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)
  exact (hn.comp (by fun_prop)).add (contDiff_const.mul (contDiff_snd.pow 2))

lemma cubicThetaMobiusNumerator_contDiff (g : SL(2,ℂ)) :
    ContDiff ℝ ∞ (cubicThetaMobiusNumerator g) := by
  have hz : ContDiff ℝ ∞ (fun p : ℂ × ℝ => g 1 0*p.1+g 1 1) := by fun_prop
  have hc : ContDiff ℝ ∞ (fun p : ℂ × ℝ => star (g 1 0*p.1+g 1 1)) := by
    simpa only [Function.comp_def,Complex.star_def,Complex.conjCLE_apply] using Complex.conjCLE.contDiff.comp hz
  exact ((by fun_prop : ContDiff ℝ ∞ (fun p : ℂ × ℝ => g 0 0*p.1+g 0 1)).mul hc).add
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_snd.pow 2)))

lemma cubicThetaMobius_contDiffAt (g : SL(2,ℂ)) {p : ℂ × ℝ} (hp : 0<p.2) :
    ContDiffAt ℝ ∞ (cubicThetaMobius g) p := by
  have hD := (cubicThetaMobiusDenominator_contDiff g).contDiffAt (x:=p)
  have hN := (cubicThetaMobiusNumerator_contDiff g).contDiffAt (x:=p)
  have hd := (cubicThetaMobius_denominator_pos g hp).ne'
  unfold cubicThetaMobius
  simp only [div_eq_mul_inv]
  exact (hN.mul ((Complex.ofRealCLM.contDiff.contDiffAt.comp p hD).inv
    (Complex.ofReal_ne_zero.mpr hd))).prodMk (contDiffAt_snd.mul (hD.inv hd))

lemma cubicThetaMobius_contDiffOn (g : SL(2,ℂ)) {S : Set (ℂ × ℝ)}
    (hS : ∀ p∈S, 0<p.2) : ContDiffOn ℝ ∞ (cubicThetaMobius g) S :=
  fun p hp => (cubicThetaMobius_contDiffAt g (hS p hp)).contDiffWithinAt

end CubicFirstMoment

end

end OAI
