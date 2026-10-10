import OAI.NumberTheory.Ostmann.Supply.GroupedCharactersReindex
import OAI.NumberTheory.Ostmann.ZeroDensity.Target

namespace OAI

noncomputable section
namespace Ostmann.Supply.GroupedCharacters
open Finset Ostmann.ZeroDensity
open scoped BigOperators

theorem weighted_primitive_error_le (Q : ℕ) (exception : Option (PrimitiveFamily Q))
    (c : PrimitiveFamily Q → ℂ) (φ : ℝ → ℝ) (X M : ℝ)
    (hc : ∀ χ, ‖c χ‖ ≤ M)
    (hexception : ∀ χ, some χ = exception → c χ = 0) :
    ‖∑ χ : PrimitiveFamily Q, c χ * smoothError χ.2.1 φ X‖ ≤
      M * totalPrimitiveError Q exception φ X := by
  calc
    _ ≤ ∑ χ : PrimitiveFamily Q, ‖c χ * smoothError χ.2.1 φ X‖ := norm_sum_le _ _
    _ ≤ _ := by
      rw [totalPrimitiveError, mul_sum]
      apply sum_le_sum
      intro χ hχ
      by_cases he : some χ = exception
      · rw [ite_eq_left he, hexception χ he, zero_mul, norm_zero, mul_zero]
      · rw [ite_eq_right he, norm_mul]
        exact mul_le_mul_of_nonneg_right (hc χ) (norm_nonneg _)

theorem grouped_primitive_error_le {α : Type*} [DecidableEq α]
    (s : Finset α) (Q : ℕ) (e : α → PrimitiveFamily Q) (c : α → ℂ)
    (he : Set.InjOn e (s : Set α)) (exception : Option (PrimitiveFamily Q))
    (havoid : ∀ i ∈ s, some (e i) ≠ exception) (φ : ℝ → ℝ) (X M : ℝ)
    (hM : 0 ≤ M) (hc : ∀ i ∈ s, ‖c i‖ ≤ M) :
    ‖∑ χ : PrimitiveFamily Q, groupedCoefficient s e c χ * smoothError χ.2.1 φ X‖ ≤
      M * totalPrimitiveError Q exception φ X := by
  apply weighted_primitive_error_le Q exception _ φ X M
  · exact norm_groupedCoefficient_le s e c he hM hc
  · intro χ hχ
    apply groupedCoefficient_not_mem
    intro hmem
    obtain ⟨i, hi, hei⟩ := mem_image.mp hmem
    exact havoid i hi (by rw [hei]; exact hχ)

end Ostmann.Supply.GroupedCharacters

end

end OAI
