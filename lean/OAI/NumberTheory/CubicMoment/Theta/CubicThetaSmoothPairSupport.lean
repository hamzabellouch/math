import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGaussMellin

namespace OAI

/-! Compact radial support gives genuine finite sums over the unique
primary squarefree/cube pairs. -/
noncomputable section
open Set
namespace CubicFirstMoment

lemma cubicThetaPrimary_smooth_support (W : ℝ→ℂ) (hW : HasCompactSupport W)
    {X : ℝ} (hX : 0<X) :
    Set.Finite {cd : CubicThetaPrimaryPair | W (norm cd.val.1*norm cd.val.2^3/X)≠0} := by
  obtain ⟨B,hB⟩ := hW.isCompact.isBounded.exists_norm_le
  have hpre : Set.Finite {cd : CubicThetaPrimaryPair |
      norm (cubicThetaPrimaryNumerator cd)≤3*(B*X)} :=
    Set.Finite.preimage cubicThetaPrimaryNumerator_injective.injOn (finite_norm_le _)
  apply hpre.subset
  intro cd hcd
  have hb := hB _ (subset_tsupport W hcd)
  have hprod : norm cd.val.1*norm cd.val.2^3≤B*X := by
    apply (div_le_iff₀ hX).mp
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hb)
  have hf := cubicThetaFrequency_sq (cubicThetaPrimaryNumerator cd)
  rw [cubicThetaPrimaryFrequency_sq] at hf
  change norm (cubicThetaPrimaryNumerator cd)≤3*(B*X)
  linarith

lemma cubicThetaPrimary_smooth_summable (a : CubicThetaPrimaryPair→ℂ)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) {X : ℝ} (hX : 0<X) :
    Summable (fun cd : CubicThetaPrimaryPair =>
      a cd*W (norm cd.val.1*norm cd.val.2^3/X)) := by
  apply summable_of_hasFiniteSupport
  apply (cubicThetaPrimary_smooth_support W hW hX).subset
  intro cd hcd
  exact (mul_ne_zero_iff.mp hcd).2

end CubicFirstMoment

end

end OAI
