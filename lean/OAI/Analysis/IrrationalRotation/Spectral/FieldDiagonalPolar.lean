import OAI.Analysis.IrrationalRotation.Rotation.FieldDiagonal
import OAI.Analysis.IrrationalRotation.Spectral.WeightedShiftPolar
import OAI.Analysis.IrrationalRotation.Spectral.PolarFactor

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal InnerProductSpace ComplexOrder
namespace Invariant233.WeightedShift
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem fieldDiagonal_nonneg (a : X → Weight) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ x, ‖a x‖ ≤ C)
    (hm : ∀ k, AEStronglyMeasurable (fun x => a x k) μ)
    (hpos : ∀ᵐ x ∂μ, ∀ k, 0 ≤ a x k) :
    0 ≤ fieldDiagonal a C hC ha hm := by
  apply ContinuousLinearMap.nonneg_iff_isPositive.mpr
  apply ContinuousLinearMap.isPositive_def.mpr
  constructor
  · intro f g
    simp only [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [fieldDiagonal_ae a C hC ha hm f,
      fieldDiagonal_ae a C hC ha hm g, hpos] with x hf hg hx
    change inner ℂ ((fieldDiagonal a C hC ha hm f) x) (g x) =
      inner ℂ (f x) ((fieldDiagonal a C hC ha hm g) x)
    rw [hf, hg]
    exact ContinuousLinearMap.nonneg_iff_isPositive.mp
      (PolarSupport.diagonal_nonneg (a x) hx) |>.isSymmetric (f x) (g x)
  · intro f
    change 0 ≤ (inner ℂ (fieldDiagonal a C hC ha hm f) f).re
    rw [L2.inner_def]
    change 0 ≤ RCLike.re (∫ x, inner ℂ ((fieldDiagonal a C hC ha hm f) x) (f x) ∂μ)
    rw [← integral_re (L2.integrable_inner (𝕜 := ℂ) (fieldDiagonal a C hC ha hm f) f)]
    apply integral_nonneg_of_ae
    filter_upwards [fieldDiagonal_ae a C hC ha hm f, hpos] with x hf hx
    rw [hf]
    exact (ContinuousLinearMap.nonneg_iff_isPositive.mp
      (PolarSupport.diagonal_nonneg (a x) hx)).re_inner_nonneg_left (f x)

theorem star_global_shift (n : ℤ) :
    star ((shift n).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ) =
      (shift (-n)).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ := by
  symm
  rw [ContinuousLinearMap.star_eq_adjoint]
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).2
  intro f g
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [fieldShift_ae (-n) f, fieldShift_ae n g] with x hf hg
  rw [hf, hg]
  have hinv : shift (-n) (f x) = (shift n).symm (f x) := by
    apply (shift n).injective
    ext k
    simp [shift_apply]
  rw [hinv]
  have h := (shift n).inner_map_map ((shift n).symm (f x)) (g x)
  simpa only [(shift n).apply_symm_apply] using h.symm

theorem global_shift_mem_unitary (n : ℤ) :
    (shift n).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ ∈
      unitary (Lp Hilbert 2 μ →L[ℂ] Lp Hilbert 2 μ) := by
  apply Unitary.mem_iff.mpr
  rw [star_global_shift, ← fieldShift_add, ← fieldShift_add]
  simpa using And.intro (fieldShift_zero (μ := μ)) (fieldShift_zero (μ := μ))

local instance fieldDiagonalPolarRealModule : Module ℝ
    (Lp Hilbert 2 μ →L[ℂ] Lp Hilbert 2 μ) :=
  Module.complexToReal (Lp Hilbert 2 μ →L[ℂ] Lp Hilbert 2 μ)

local instance fieldDiagonalPolarFunctionalCalculus : NonUnitalContinuousFunctionalCalculus ℝ
    (Lp Hilbert 2 μ →L[ℂ] Lp Hilbert 2 μ) IsSelfAdjoint := by
  infer_instance

theorem abs_global_shift_mul_fieldDiagonal (n : ℤ) (a : X → Weight)
    (C : ℝ) (hC : 0 ≤ C) (ha : ∀ x, ‖a x‖ ≤ C)
    (hm : ∀ k, AEStronglyMeasurable (fun x => a x k) μ)
    (hpos : ∀ᵐ x ∂μ, ∀ k, 0 ≤ a x k) :
    CFC.abs ((shift n).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ *
      fieldDiagonal a C hC ha hm) = fieldDiagonal a C hC ha hm :=
  PolarFactor.abs_unitary_mul_of_nonneg
    ⟨_, global_shift_mem_unitary n⟩ _ (fieldDiagonal_nonneg a C hC ha hm hpos)

end Invariant233.WeightedShift

end

end OAI
