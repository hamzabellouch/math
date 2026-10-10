import OAI.Analysis.IrrationalRotation.Model.Product
import OAI.Analysis.IrrationalRotation.Model.ConcreteSpectral
import OAI.Analysis.IrrationalRotation.Spectral.FieldDiagonalPolar

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal ComplexOrder
namespace Invariant233.ProductModel.GlobalPolarSupport

local instance productPolarModulusComplexRealModule : Module ℝ (Hilbert →L[ℂ] Hilbert) :=
  Module.complexToReal (Hilbert →L[ℂ] Hilbert)

local instance productPolarModulusComplexFunctionalCalculus :
    NonUnitalContinuousFunctionalCalculus ℝ (Hilbert →L[ℂ] Hilbert) IsSelfAdjoint := by
  infer_instance

theorem multiplier_nonneg (θ : ℕ → ℝ) (g : Base → ℂ) (C : ℝ)
    (hC : 0 ≤ C) (hg : Measurable g) (hb : ∀ x, ‖g x‖ ≤ C)
    (hpos : ∀ x, 0 ≤ g x) : 0 ≤ multiplier θ g C hC hg hb := by
  apply WeightedShift.fieldDiagonal_nonneg
  exact Filter.Eventually.of_forall fun x k => hpos (rotationIterate θ k x)

theorem operatorModulus_shift_mul_multiplier (θ : ℕ → ℝ) (g : Base → ℂ)
    (C : ℝ) (hC : 0 ≤ C) (hg : Measurable g) (hb : ∀ x, ‖g x‖ ≤ C)
    (hpos : ∀ x, 0 ≤ g x) :
    operatorModulus (shiftOperator * multiplier θ g C hC hg hb) =
      multiplier θ g C hC hg hb := by
  change CFC.abs (shiftOperator * multiplier θ g C hC hg hb) = _
  apply WeightedShift.abs_global_shift_mul_fieldDiagonal
  exact Filter.Eventually.of_forall fun x k => hpos (rotationIterate θ k x)

theorem shiftOperator_mem_unitary : shiftOperator ∈ unitary (Hilbert →L[ℂ] Hilbert) :=
  WeightedShift.global_shift_mem_unitary 1

theorem weightedOperator_eq_shift_mul_modulus (θ c : ℕ → ℝ) :
    weightedOperator θ c = shiftOperator * operatorModulus (weightedOperator θ c) := by
  simp only [weightedOperator, ← ContinuousLinearMap.mul_def]
  rw [operatorModulus_shift_mul_multiplier]
  intro x
  exact Complex.nonneg_iff.mpr ⟨ENNReal.toReal_nonneg, rfl⟩

theorem operatorModulus_weightedOperator (θ c : ℕ → ℝ)
    (hg : Measurable fun x => (weight θ c x : ℂ))
    (hb : ∀ x, ‖(weight θ c x : ℂ)‖ ≤ 1) :
    operatorModulus (weightedOperator θ c) =
      multiplier θ (fun x => (weight θ c x : ℂ)) 1 (by norm_num) hg hb := by
  change operatorModulus (shiftOperator *
    multiplier θ (fun x => (weight θ c x : ℂ)) 1 (by norm_num) hg hb) = _
  apply operatorModulus_shift_mul_multiplier
  intro x
  exact Complex.nonneg_iff.mpr ⟨ENNReal.toReal_nonneg, rfl⟩

end Invariant233.ProductModel.GlobalPolarSupport

end

end OAI
