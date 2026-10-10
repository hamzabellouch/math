import OAI.Analysis.FiniteFactor.BiasedPairs.RealIdentity
import OAI.Analysis.FiniteFactor.Fiber.ProjectionDiagonal
import OAI.Analysis.FiniteFactor.Convolution

namespace OAI

namespace FiniteFactor
open MeasureTheory
open scoped ComplexConjugate
noncomputable section

def sourceProjectionColumn
    (p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate)
    (x : SourceCoordinate → ℝ) : SourceFiberHilbert := sourceOperatorField p x (lp.single 2 0 (1 : ℂ))

def sourceComplementColumn
    (p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate)
    (x : SourceCoordinate → ℝ) : SourceFiberHilbert := (1-sourceOperatorField p x) (lp.single 2 0 (1 : ℂ))

def sourceProjectionLeftCoefficient (θ : SourceCoordinate → ℝ)
    (p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate)
    (x : SourceCoordinate → ℝ) (k : ℤ) : ℂ :=
  leftCoefficient (fun k => sourceCocycle θ sourceLogWeight k x) (sourceProjectionColumn p x) k

def sourceProjectionRightCoefficient (θ : SourceCoordinate → ℝ)
    (p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate)
    (y : SourceCoordinate → ℝ) (k : ℤ) : ℂ :=
  rightCoefficient (fun k => sourceCocycle θ sourceLogWeight k y) (sourceComplementColumn p y) k

theorem fiberProjection_column_norm_le_one
    (P : SourceFiberHilbert →L[ℂ] SourceFiberHilbert) (hP : IsStarProjection P) (k : ℤ) :
    ‖P (lp.single 2 k (1 : ℂ))‖ ≤ 1 := by
  have hd := (fiberProjection_diagonal_bounds P hP k).2.1
  have he := congrArg Complex.re (fiberProjection_diagonal_inner P hP k)
  rw [show ∀ v : SourceFiberHilbert, (inner ℂ v v).re = ‖v‖^2 from inner_self_eq_norm_sq (𝕜 := ℂ)] at he
  nlinarith [norm_nonneg (P (lp.single 2 k (1 : ℂ)))]

theorem sourceProjection_columns_norm (θ : SourceCoordinate → ℝ)
    {p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hp : p ∈ sourceAlgebra θ) (hproj : IsStarProjection p) :
    ∀ᵐ x ∂sourceBaseMeasure, ‖sourceProjectionColumn p x‖ ≤ 1 ∧ ‖sourceComplementColumn p x‖ ≤ 1 := by
  filter_upwards [sourceOperatorField_projection θ hp hproj] with x hx
  exact ⟨fiberProjection_column_norm_le_one _ hx 0,fiberProjection_column_norm_le_one _ hx.one_sub 0⟩

theorem sourceProjectionLeftCoefficient_measurable (θ : SourceCoordinate → ℝ)
    (p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) (k : ℤ) :
    Measurable (fun x => sourceProjectionLeftCoefficient θ p x k) :=
  (sourceOperatorField_entry_measurable p k 0).div
    (Complex.continuous_ofReal.measurable.comp (sourceCocycle_measurable θ sourceLogWeight k))

theorem sourceProjectionRightCoefficient_measurable (θ : SourceCoordinate → ℝ)
    (p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) (k : ℤ) :
    Measurable (fun y => sourceProjectionRightCoefficient θ p y k) := by
  apply (Complex.continuous_ofReal.measurable.comp (sourceCocycle_measurable θ sourceLogWeight (-k))).mul
  exact Complex.continuous_conj.measurable.comp
    (measurable_const.sub (sourceOperatorField_entry_measurable p (-k) 0))

end
end FiniteFactor

end OAI
