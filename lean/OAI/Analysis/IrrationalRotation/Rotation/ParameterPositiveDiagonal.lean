import OAI.Analysis.IrrationalRotation.Rotation.RealWeightedPositiveDiagonal
import OAI.Analysis.IrrationalRotation.Analysis.ParameterOrbitIdentity
import OAI.Analysis.IrrationalRotation.Analysis.RationalGraphs
import OAI.Analysis.IrrationalRotation.Rotation.RotationTrace
import OAI.Analysis.IrrationalRotation.Operators.FaithfulProjectionTrace

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal InnerProductSpace

namespace Invariant233.CircleParameterLaws

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)

theorem ae_strict_diagonal_measurableOperator (hθ : Irrational θ)
    (P : Rotation.Hilbert →L[ℂ] Rotation.Hilbert)
    (hPm : P ∈ Rotation.algebra θ) (hP : IsStarProjection P)
    (hinv : (1 - P) * p.measurableOperator θ hp * P = 0)
    (htrace0 : 0 < (Rotation.vacuumFunctional P).re)
    (htrace1 : (Rotation.vacuumFunctional P).re < 1)
    (F : Circle → Rotation.Fiber →L[ℂ] Rotation.Fiber)
    (hbound : ∀ x, ‖F x‖ ≤ ‖P‖)
    (hmeas : ∀ v, StronglyMeasurable fun x => F x v)
    (hrep : ∀ ξ : Rotation.Hilbert, P ξ =ᵐ[circleMeasure] fun x => F x (ξ x)) :
    ∀ᵐ x ∂circleMeasure,
      0 < (inner ℂ PositiveDiagonalModel.e0 (F x PositiveDiagonalModel.e0)).re ∧
      (inner ℂ PositiveDiagonalModel.e0 (F x PositiveDiagonalModel.e0)).re < 1 := by
  let b : HilbertBasis ℤ ℂ Rotation.Fiber :=
    HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ Rotation.Fiber)
  let D : Circle → Rotation.Fiber →L[ℂ] Rotation.Fiber :=
    fun x => WeightedShift.diagonal (hp.parameterOrbitWeight x)
  let a : Circle → ℤ → ℝ := fun x k => p.measurableWeight θ (Rotation.action θ k x)
  have hb : ∀ x k, |a x k| ≤ 1 := by
    intro x k
    simpa only [Complex.norm_real, Real.norm_eq_abs] using
      p.measurableWeight_operator_bound θ hp (Rotation.action θ k x)
  have hw (x : Circle) : hp.parameterOrbitWeight x =
      PositiveDiagonalModel.realWeight a 1 hb x := by
    ext k
    rfl
  have hD : ∀ᵐ x ∂circleMeasure, IsSelfAdjoint (D x) := by
    apply Eventually.of_forall
    intro x
    dsimp [D]
    rw [hw]
    exact PositiveDiagonalModel.realWeight_diagonal_selfAdjoint a 1 hb x
  have heigen : ∀ᵐ x ∂circleMeasure,
      D x PositiveDiagonalModel.e0 =
        (p.measurableWeight θ x : ℂ) • PositiveDiagonalModel.e0 := by
    apply Eventually.of_forall
    intro x
    dsimp [D]
    rw [hw]
    simpa only [a, Rotation.action_zero, Complex.coe_smul] using
      PositiveDiagonalModel.realWeight_diagonal_e0 a 1 hb x
  have hT : ∀ ξ : Rotation.Hilbert, p.measurableOperator θ hp ξ =ᵐ[circleMeasure]
      fun x => ((PositiveDiagonalModel.fiberShiftUnit : Rotation.Fiber →L[ℂ] Rotation.Fiber) * D x) (ξ x) := by
    intro ξ
    exact hp.measurableOperator_ae ξ
  have hcov := DirectIntegral.ae_covariance_of_represented_commute b P F
    PositiveDiagonalModel.fiberShift (Rotation.action θ 1)
    (Rotation.action_measurePreserving θ 1) hrep
    (Rotation.algebra_commutes_shiftedPullback_int_independent θ 1 hPm)
  have hcov' : ∀ᵐ x ∂circleMeasure, F (Rotation.action θ 1 x) =
      ↑(PositiveDiagonalModel.fiberShiftUnit⁻¹) * F x *
        (PositiveDiagonalModel.fiberShiftUnit : Rotation.Fiber →L[ℂ] Rotation.Fiber) := by
    filter_upwards [hcov] with x hx
    have hh := congrArg (fun A : Rotation.Fiber →L[ℂ] Rotation.Fiber =>
      (↑(PositiveDiagonalModel.fiberShiftUnit⁻¹) : Rotation.Fiber →L[ℂ] Rotation.Fiber) * A) hx
    simpa only [← PositiveDiagonalModel.coe_fiberShiftUnit, ← mul_assoc,
      Units.inv_mul, one_mul] using hh.symm
  exact Fields.ae_strict_diagonal_of_represented_weighted_shift b
    (Rotation.action_one_ergodic hθ) P (p.measurableOperator θ hp) F D
    PositiveDiagonalModel.fiberShiftUnit ‖P‖ (norm_nonneg P) hbound hmeas hrep
    hT hP hinv hcov' PositiveDiagonalModel.norm_e0 hD
    (Eventually.of_forall (fun x => ne_of_gt (Real.exp_pos _)))
    heigen htrace0 htrace1

theorem ae_strict_diagonal_measurableOperator_of_nontrivial (hθ : Irrational θ)
    (P : Rotation.Hilbert →L[ℂ] Rotation.Hilbert)
    (hPm : P ∈ Rotation.algebra θ) (hP : IsStarProjection P)
    (hinv : (1 - P) * p.measurableOperator θ hp * P = 0)
    (hP0 : P ≠ 0) (hP1 : P ≠ 1)
    (F : Circle → Rotation.Fiber →L[ℂ] Rotation.Fiber)
    (hbound : ∀ x, ‖F x‖ ≤ ‖P‖)
    (hmeas : ∀ v, StronglyMeasurable fun x => F x v)
    (hrep : ∀ ξ : Rotation.Hilbert, P ξ =ᵐ[circleMeasure] fun x => F x (ξ x)) :
    ∀ᵐ x ∂circleMeasure,
      0 < (inner ℂ PositiveDiagonalModel.e0 (F x PositiveDiagonalModel.e0)).re ∧
      (inner ℂ PositiveDiagonalModel.e0 (F x PositiveDiagonalModel.e0)).re < 1 := by
  have htrace := strict_trace_bounds_of_nontrivial_projection
    (Rotation.algebra θ) Rotation.vacuum (Rotation.vacuum_faithfulTracial θ)
    P hPm hP hP0 hP1
  exact hp.ae_strict_diagonal_measurableOperator hθ P hPm hP hinv
    htrace.1 htrace.2 F hbound hmeas hrep

theorem exists_strict_rational_graph_field (hθ : Irrational θ)
    {P : Rotation.Hilbert →L[ℂ] Rotation.Hilbert}
    (hPm : P ∈ Rotation.algebra θ) (hP : IsStarProjection P)
    (hinv : (1 - P) * p.measurableOperator θ hp * P = 0)
    (hP0 : P ≠ 0) (hP1 : P ≠ 1) :
    ∃ F : Circle → Rotation.Fiber →L[ℂ] Rotation.Fiber,
      (∀ x, IsStarProjection (F x)) ∧
      (∀ x, ‖F x‖ ≤ ‖P‖) ∧
      (∀ v, StronglyMeasurable fun x => F x v) ∧
      (∀ ξ : Rotation.Hilbert, P ξ =ᵐ[circleMeasure] fun x => F x (ξ x)) ∧
      p.RationalGraphIdentities θ F ∧
      (∀ᵐ x ∂circleMeasure,
        0 < (inner ℂ PositiveDiagonalModel.e0 (F x PositiveDiagonalModel.e0)).re ∧
        (inner ℂ PositiveDiagonalModel.e0 (F x PositiveDiagonalModel.e0)).re < 1) := by
  obtain ⟨F, hproj, hbound, hmeas, hrep, hgraph⟩ :=
    hp.exists_rational_graph_field hPm hP hinv
  exact ⟨F, hproj, hbound, hmeas, hrep, hgraph,
    hp.ae_strict_diagonal_measurableOperator_of_nontrivial hθ P hPm hP hinv
      hP0 hP1 F hbound hmeas hrep⟩

end Invariant233.CircleParameterLaws

end

end OAI
