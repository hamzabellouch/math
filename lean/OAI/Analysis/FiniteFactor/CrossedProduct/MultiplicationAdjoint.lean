import OAI.Analysis.FiniteFactor.CrossedProduct.GeneratedAlgebra
import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
noncomputable section

/-- Conjugate of a bounded source base function, with the same bound. -/
def sourceBaseStar (g : SourceBaseFunction) : SourceBaseFunction where
  toFun := fun x => star (g.toFun x)
  measurable := Complex.continuous_conj.measurable.comp g.measurable
  bound := g.bound
  bound_nonneg := g.bound_nonneg
  norm_le := by intro x hx; simpa using g.norm_le x hx

/-- The multiplication representation has the actual Hilbert adjoint. -/
theorem sourcePi_star (θ : SourceCoordinate → ℝ) (g : SourceBaseFunction) :
    star (sourcePi θ g) = sourcePi θ (sourceBaseStar g) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro f h
  change (∫ z, inner ℂ ((sourcePi θ (sourceBaseStar g) f) z) (h z) ∂sourceMeasure SourceCoordinate) =
    ∫ z, inner ℂ (f z) ((sourcePi θ g h) z) ∂sourceMeasure SourceCoordinate
  apply integral_congr_ae
  filter_upwards [sourcePi_apply_ae θ (sourceBaseStar g) f,
    sourcePi_apply_ae θ g h] with z hf hh
  rw [hf, hh]
  simp [sourcePiSymbol, sourceBaseStar, RCLike.inner_apply, mul_comm, mul_left_comm, mul_assoc]

/-- Any two such multiplication operators commute, even for different angles. -/
theorem sourcePi_commute (θ φ : SourceCoordinate → ℝ) (g h : SourceBaseFunction) :
    sourcePi θ g * sourcePi φ h = sourcePi φ h * sourcePi θ g := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [sourcePi_apply_ae θ g (sourcePi φ h f),
    sourcePi_apply_ae φ h f, sourcePi_apply_ae φ h (sourcePi θ g f),
    sourcePi_apply_ae θ g f] with z hg hh hg' hh'
  change (sourcePi θ g (sourcePi φ h f)) z = (sourcePi φ h (sourcePi θ g f)) z
  rw [hg, hh, hg', hh']
  ring

end
end FiniteFactor

end OAI
