import OAI.NumberTheory.CubicMoment.Theta.CubicThetaMobiusAction

namespace OAI

/-! Continuity of the actual hyperbolic matrix action, used to transport
compact core charts. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaMobiusDenominator_continuous (g : SL(2,ℂ)) :
    Continuous (cubicThetaMobiusDenominator g) := by
  unfold cubicThetaMobiusDenominator
  fun_prop

lemma cubicThetaMobiusNumerator_continuous (g : SL(2,ℂ)) :
    Continuous (cubicThetaMobiusNumerator g) := by
  unfold cubicThetaMobiusNumerator
  fun_prop

lemma cubicThetaMobius_continuousAt (g : SL(2,ℂ)) {p : ℂ × ℝ} (hp : 0<p.2) :
    ContinuousAt (cubicThetaMobius g) p := by
  have hD := (cubicThetaMobiusDenominator_continuous g).continuousAt (x:=p)
  have hN := (cubicThetaMobiusNumerator_continuous g).continuousAt (x:=p)
  have hd := (cubicThetaMobius_denominator_pos g hp).ne'
  unfold cubicThetaMobius
  exact (hN.div (Complex.continuous_ofReal.continuousAt.comp hD)
    (Complex.ofReal_ne_zero.mpr hd)).prodMk (continuous_snd.continuousAt.div hD hd)

lemma cubicThetaMobius_continuousOn (g : SL(2,ℂ)) {S : Set (ℂ × ℝ)}
    (hS : ∀ p∈S, 0<p.2) : ContinuousOn (cubicThetaMobius g) S :=
  fun p hp => (cubicThetaMobius_continuousAt g (hS p hp)).continuousWithinAt

end CubicFirstMoment

end

end OAI
