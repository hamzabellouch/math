import OAI.Analysis.IrrationalRotation.Spectral.ProductFinitePolar
import OAI.Analysis.IrrationalRotation.Spectral.ProductPolarRange

namespace OAI

noncomputable section
open MeasureTheory Set

namespace Invariant233.ProductModel

theorem weight_complex_norm_le_one (θ c : ℕ → ℝ) (x : Base) :
    ‖(weight θ c x : ℂ)‖ ≤ 1 := by
  simpa only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (weight_mem_Icc θ c x).1] using (weight_mem_Icc θ c x).2

theorem star_shift_weightedOperator_eq_multiplier (θ c : ℕ → ℝ) :
    star shiftOperator * weightedOperator θ c =
      multiplier θ (fun x ↦ (weight θ c x : ℂ)) 1 (by norm_num)
        (measurable_weight θ c).complex_ofReal (weight_complex_norm_le_one θ c) := by
  have hu : star shiftOperator * shiftOperator = 1 :=
    (Unitary.mem_iff.mp (WeightedShift.fieldShift_mem_unitary (μ := baseMeasure) 1)).1
  simp only [weightedOperator, ← ContinuousLinearMap.mul_def]
  rw [← mul_assoc, hu, one_mul]

theorem finitePolarAlgebra_weight_atomic (θ c : ℕ → ℝ)
    (hθ01 : ∀ i, θ i ∈ Ico (0 : ℝ) 1) (hc : ∀ i, 0 ≤ c i)
    (hθ : Summable θ) (F : Finset ℤ) :
    IsAbelianVonNeumannAlgebra
      (finitePolarAlgebra shiftOperator (star shiftOperator * weightedOperator θ c) F) ∧
    IsAtomicVonNeumannAlgebra
      (finitePolarAlgebra shiftOperator (star shiftOperator * weightedOperator θ c) F) := by
  rw [star_shift_weightedOperator_eq_multiplier]
  obtain ⟨S, hS, -, hmem⟩ := ae_weight_mem_countable θ c hθ01 hc hθ
  exact finitePolarAlgebra_multiplier_atomic θ (weight θ c) 1 (by norm_num)
    (measurable_weight θ c) (weight_complex_norm_le_one θ c) ⟨S, hS, hmem⟩ F

theorem fullPolarAlgebra_weight_abelian (θ c : ℕ → ℝ) :
    IsAbelianVonNeumannAlgebra
      (fullPolarAlgebra shiftOperator (star shiftOperator * weightedOperator θ c)) := by
  rw [star_shift_weightedOperator_eq_multiplier]
  exact fullPolarAlgebra_multiplier_abelian θ (weight θ c) 1 (by norm_num)
    (measurable_weight θ c) (weight_complex_norm_le_one θ c)

theorem weight_hasCountablyAtomicSpectralType (θ c : ℕ → ℝ)
    (hθ01 : ∀ i, θ i ∈ Ico (0 : ℝ) 1) (hc : ∀ i, 0 ≤ c i)
    (hθ : Summable θ) :
    HasCountablyAtomicSpectralType (star shiftOperator * weightedOperator θ c) := by
  rw [star_shift_weightedOperator_eq_multiplier]
  obtain ⟨S, hS, -, hmem⟩ := ae_weight_mem_countable θ c hθ01 hc hθ
  exact multiplier_hasCountablyAtomicSpectralType θ (weight θ c) 1 (by norm_num)
    (measurable_weight θ c) (weight_complex_norm_le_one θ c) ⟨S, hS, hmem⟩

theorem weight_multiplier_injective (θ c : ℕ → ℝ)
    (hθ0 : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) (hθ : Summable θ) :
    Function.Injective (star shiftOperator * weightedOperator θ c) := by
  rw [star_shift_weightedOperator_eq_multiplier]
  apply multiplier_injective_of_ae_ne_zero
  filter_upwards [ae_weight_pos θ c hθ0 hc hθ] with x hx
  exact_mod_cast hx.ne'

end Invariant233.ProductModel

end

end OAI
