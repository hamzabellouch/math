import OAI.Analysis.IrrationalRotation.Rotation.RealWeightedPositiveDiagonal
import OAI.Analysis.IrrationalRotation.Rotation.RotationCenter

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal InnerProductSpace

namespace Invariant233.Rotation

theorem ae_strict_diagonal_of_invariant_projection
    {θ : ℝ} (hθ : Irrational θ) (f : C(Circle, ℝ))
    (hf : ∀ᵐ x ∂circleMeasure, 0 < f x)
    (P : Hilbert →L[ℂ] Hilbert) (hPm : P ∈ algebra θ) (hP : IsStarProjection P)
    (hinv : (1 - P) * weightedReal θ f * P = 0)
    (htrace0 : 0 < (vacuumFunctional P).re) (htrace1 : (vacuumFunctional P).re < 1)
    (p : Circle → Fiber →L[ℂ] Fiber)
    (hpbound : ∀ x, ‖p x‖ ≤ ‖P‖)
    (hpm : ∀ v, StronglyMeasurable fun x => p x v)
    (hrep : ∀ ξ : Hilbert, P ξ =ᵐ[circleMeasure] fun x => p x (ξ x)) :
    ∀ᵐ x ∂circleMeasure,
      0 < (inner ℂ PositiveDiagonalModel.e0 (p x PositiveDiagonalModel.e0)).re ∧
      (inner ℂ PositiveDiagonalModel.e0 (p x PositiveDiagonalModel.e0)).re < 1 := by
  let b : HilbertBasis ℤ ℂ Fiber :=
    HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ Fiber)
  let D : Circle → Fiber →L[ℂ] Fiber :=
    fun x => WeightedShift.diagonal (orbitWeight θ (complexWeight f) x)
  let a : Circle → ℤ → ℝ := fun x k => f (action θ k x)
  have hb : ∀ x k, |a x k| ≤ ‖f‖ := by
    intro x k
    exact (Real.norm_eq_abs _).symm ▸ f.norm_coe_le_norm (action θ k x)
  have hw (x : Circle) : orbitWeight θ (complexWeight f) x =
      PositiveDiagonalModel.realWeight a ‖f‖ hb x := by
    ext k
    rfl
  have hD : ∀ᵐ x ∂circleMeasure, IsSelfAdjoint (D x) := by
    apply Eventually.of_forall
    intro x
    dsimp [D]
    rw [hw]
    exact PositiveDiagonalModel.realWeight_diagonal_selfAdjoint a ‖f‖ hb x
  have heigen : ∀ᵐ x ∂circleMeasure,
      D x PositiveDiagonalModel.e0 = (f x : ℂ) • PositiveDiagonalModel.e0 := by
    apply Eventually.of_forall
    intro x
    dsimp [D]
    rw [hw]
    simpa only [a, action_zero, Complex.coe_smul] using
      PositiveDiagonalModel.realWeight_diagonal_e0 a ‖f‖ hb x
  have hT : ∀ ξ : Hilbert, weightedReal θ f ξ =ᵐ[circleMeasure] fun x =>
      ((PositiveDiagonalModel.fiberShiftUnit : Fiber →L[ℂ] Fiber) * D x) (ξ x) := by
    intro ξ
    filter_upwards [U_ae (representation θ (complexWeight f) ξ),
      representation_ae θ (complexWeight f) ξ] with x hs hd
    exact hs.trans (congrArg (WeightedShift.shift 1) hd)
  have hcov := DirectIntegral.ae_covariance_of_represented_commute b P p
    PositiveDiagonalModel.fiberShift (action θ 1) (action_measurePreserving θ 1)
    hrep (algebra_commutes_shiftedPullback_int_independent θ 1 hPm)
  have hcov' : ∀ᵐ x ∂circleMeasure, p (action θ 1 x) =
      ↑(PositiveDiagonalModel.fiberShiftUnit⁻¹) * p x *
        (PositiveDiagonalModel.fiberShiftUnit : Fiber →L[ℂ] Fiber) := by
    filter_upwards [hcov] with x hx
    have hh := congrArg (fun A : Fiber →L[ℂ] Fiber =>
      (↑(PositiveDiagonalModel.fiberShiftUnit⁻¹) : Fiber →L[ℂ] Fiber) * A) hx
    simpa only [← PositiveDiagonalModel.coe_fiberShiftUnit, ← mul_assoc,
      Units.inv_mul, one_mul] using hh.symm
  exact Fields.ae_strict_diagonal_of_represented_weighted_shift b
    (action_one_ergodic hθ) P (weightedReal θ f) p D
    PositiveDiagonalModel.fiberShiftUnit ‖P‖ (norm_nonneg P) hpbound hpm hrep
    hT hP hinv hcov' PositiveDiagonalModel.norm_e0 hD
    (hf.mono fun _ hx => ne_of_gt hx) heigen htrace0 htrace1

theorem exists_strict_projection_field
    {θ : ℝ} (hθ : Irrational θ) (f : C(Circle, ℝ))
    (hf : ∀ᵐ x ∂circleMeasure, 0 < f x)
    (P : Hilbert →L[ℂ] Hilbert) (hPm : P ∈ algebra θ) (hP : IsStarProjection P)
    (hinv : (1 - P) * weightedReal θ f * P = 0)
    (htrace0 : 0 < (vacuumFunctional P).re) (htrace1 : (vacuumFunctional P).re < 1) :
    ∃ p : Circle → Fiber →L[ℂ] Fiber,
      (∀ x, ‖p x‖ ≤ ‖P‖) ∧
      (∀ v, StronglyMeasurable fun x => p x v) ∧
      (∀ ξ : Hilbert, P ξ =ᵐ[circleMeasure] fun x => p x (ξ x)) ∧
      (∀ᵐ x ∂circleMeasure, IsStarProjection (p x)) ∧
      (∀ᵐ x ∂circleMeasure,
        0 < (inner ℂ PositiveDiagonalModel.e0 (p x PositiveDiagonalModel.e0)).re ∧
        (inner ℂ PositiveDiagonalModel.e0 (p x PositiveDiagonalModel.e0)).re < 1) := by
  obtain ⟨p, hpbound, hpm, hrep, _⟩ := exists_unique_field hPm
  refine ⟨p, hpbound, hpm, hrep, ?_,
    ae_strict_diagonal_of_invariant_projection hθ f hf P hPm hP hinv
      htrace0 htrace1 p hpbound hpm hrep⟩
  exact DirectIntegral.ae_isStarProjection_of_representation
    (default : HilbertBasis ℤ ℂ Fiber) P p ‖P‖ (norm_nonneg P) hpbound hpm hrep hP

end Invariant233.Rotation

end

end OAI
