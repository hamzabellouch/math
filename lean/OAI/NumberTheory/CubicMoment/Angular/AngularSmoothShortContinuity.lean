import OAI.NumberTheory.CubicMoment.Angular.AngularShortTupleMellin
import OAI.NumberTheory.CubicMoment.Estimates.SmoothShortContinuity
import OAI.NumberTheory.CubicMoment.Estimates.MellinMomentTransfer

namespace OAI

/-! Continuity and Mellin weights for actual finite smooth short sums. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem continuous_primaryAngularShortSmoothSum (ℓ : ℤ) (A : EisensteinArithmeticFunction)
    (a b q : Eisenstein) (η : MulChar (Residues q) ℂ) (W : ℝ → ℂ)
    {X : ℝ} (hX : 0 < X) (hW : ∀ x : ℝ, 2 < x → W x = 0) :
    Continuous (primaryAngularShortSmoothSum ℓ A a b q η W (X/2)) := by
  have he := funext (primaryAngularShortSmoothSum_eq_subtype ℓ A a b q η W hX hW)
  rw [he]
  apply continuous_finsetSum
  intro n _
  unfold mellinPhase
  fun_prop

end CubicFirstMoment

end

end OAI
