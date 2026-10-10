import OAI.Analysis.IrrationalRotation.Model.PositiveDiagonalModel
import OAI.Analysis.IrrationalRotation.Rotation.RepresentedPositiveDiagonal
import OAI.Analysis.IrrationalRotation.Rotation.WeightedShiftAlgebra

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal InnerProductSpace

namespace Invariant233.PositiveDiagonalModel

@[simp] theorem coe_fiberShiftUnit :
    (fiberShiftUnit : Fiber →L[ℂ] Fiber) = fiberShift := rfl

@[simp] theorem norm_e0 : ‖e0‖ = 1 := by
  simp [e0, lp.norm_single (by norm_num : (0 : ENNReal) < 2)]

variable {Y : Type*} [MeasurableSpace Y] {μ : Measure Y}

theorem realWeightedShift_ae
    (a : Y → ℤ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ y k, |a y k| ≤ C)
    (hm : ∀ k, AEStronglyMeasurable (fun y => a y k) μ)
    (ξ : Space μ) :
    realWeightedShift a C hC hbound hm ξ =ᵐ[μ] fun y =>
      (fiberShift * WeightedShift.diagonal (realWeight a C hbound y)) (ξ y) := by
  have hdiag := WeightedShift.fieldDiagonalVec_ae (realWeight a C hbound) C hC
    (fun y => lp.norm_le_of_forall_le hC (fun k => by
      simpa only [realWeight, Complex.norm_real, Real.norm_eq_abs] using hbound y k))
    (fun k => Complex.continuous_ofReal.comp_aestronglyMeasurable (hm k)) ξ
  filter_upwards [fiberShift.coeFn_compLpL (realDiagonal a C hC hbound hm ξ), hdiag]
    with y hs hd
  exact hs.trans (congrArg fiberShift hd)

omit [MeasurableSpace Y] in
theorem realWeight_diagonal_selfAdjoint
    (a : Y → ℤ → ℝ) (C : ℝ) (hbound : ∀ y k, |a y k| ≤ C) (y : Y) :
    IsSelfAdjoint (WeightedShift.diagonal (realWeight a C hbound y)) := by
  rw [isSelfAdjoint_iff, ← WeightedShift.diagonal_star]
  congr 1
  ext k
  simp [realWeight, lp.star_apply]

omit [MeasurableSpace Y] in
theorem realWeight_diagonal_e0
    (a : Y → ℤ → ℝ) (C : ℝ) (hbound : ∀ y k, |a y k| ≤ C) (y : Y) :
    WeightedShift.diagonal (realWeight a C hbound y) e0 = (a y 0 : ℂ) • e0 := by
  ext k
  change (a y k : ℂ) * (lp.single (E := fun _ : ℤ => ℂ) 2 0 1) k =
    (a y 0 : ℂ) * (lp.single (E := fun _ : ℤ => ℂ) 2 0 1) k
  by_cases hk : k = 0
  · subst k
    rfl
  · simp [lp.single_apply, hk]

theorem positive_diagonal
    [IsProbabilityMeasure μ] {σ : Y → Y} (hσ : Ergodic σ μ)
    (a : Y → ℤ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ y k, |a y k| ≤ C)
    (hm : ∀ k, AEStronglyMeasurable (fun y => a y k) μ)
    (hpositive : ∀ᵐ y ∂μ, 0 < a y 0)
    (P : Space μ →L[ℂ] Space μ) (p : Y → Fiber →L[ℂ] Fiber)
    (hpbound : ∀ y, ‖p y‖ ≤ ‖P‖)
    (hpm : ∀ v, StronglyMeasurable fun y => p y v)
    (hrep : ∀ ξ : Space μ, P ξ =ᵐ[μ] fun y => p y (ξ y))
    (hP : IsStarProjection P)
    (hcov : ∀ᵐ y ∂μ, p y * fiberShift = fiberShift * p (σ y))
    (hinv : (1 - P) * realWeightedShift a C hC hbound hm * P = 0)
    (htrace0 : 0 < diagonalState P) (htrace1 : diagonalState P < 1) :
    ∀ᵐ y ∂μ, 0 < (inner ℂ e0 (p y e0)).re ∧
      (inner ℂ e0 (p y e0)).re < 1 := by
  let b : HilbertBasis ℤ ℂ Fiber :=
    HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ Fiber)
  apply Fields.ae_strict_diagonal_of_represented_weighted_shift b hσ P
    (realWeightedShift a C hC hbound hm) p
    (fun y => WeightedShift.diagonal (realWeight a C hbound y))
    fiberShiftUnit ‖P‖ (norm_nonneg P) hpbound hpm hrep
    (realWeightedShift_ae a C hC hbound hm) hP hinv
    ?_ norm_e0 (Eventually.of_forall (realWeight_diagonal_selfAdjoint a C hbound))
    (hpositive.mono fun _ hy => ne_of_gt hy)
    (Eventually.of_forall (realWeight_diagonal_e0 a C hbound)) htrace0 htrace1
  filter_upwards [hcov] with y hy
  have hh := congrArg (fun A : Fiber →L[ℂ] Fiber =>
    (↑(fiberShiftUnit⁻¹) : Fiber →L[ℂ] Fiber) * A) hy
  simpa only [← coe_fiberShiftUnit, ← mul_assoc, Units.inv_mul, one_mul] using hh.symm

theorem positive_diagonal_orbit
    [IsProbabilityMeasure μ] (σ : Y ≃ᵐ Y) (hσ : Ergodic σ μ)
    (f : Y → ℝ) (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ y, |f y| ≤ C) (hpositive : ∀ᵐ y ∂μ, 0 < f y)
    (P : Space μ →L[ℂ] Space μ) (p : Y → Fiber →L[ℂ] Fiber)
    (hpbound : ∀ y, ‖p y‖ ≤ ‖P‖)
    (hpm : ∀ v, StronglyMeasurable fun y => p y v)
    (hrep : ∀ ξ : Space μ, P ξ =ᵐ[μ] fun y => p y (ξ y))
    (hP : IsStarProjection P)
    (hcov : ∀ᵐ y ∂μ, p y * fiberShift = fiberShift * p (σ y))
    (hinv : (1 - P) * orbitWeightedShift σ f C hC hbound hf * P = 0)
    (htrace0 : 0 < diagonalState P) (htrace1 : diagonalState P < 1) :
    ∀ᵐ y ∂μ, 0 < (inner ℂ e0 (p y e0)).re ∧
      (inner ℂ e0 (p y e0)).re < 1 := by
  apply positive_diagonal hσ (orbitArray σ f) C hC
    (fun y k => hbound (integerIterate σ k y))
    (fun k => (hf.comp (measurable_integerIterate σ k)).aestronglyMeasurable)
    ?_ P p hpbound hpm hrep hP hcov hinv htrace0 htrace1
  simpa only [orbitArray, integerIterate, Function.iterate_zero, id_eq] using hpositive

end Invariant233.PositiveDiagonalModel

end

end OAI
