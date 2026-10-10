import Mathlib.Topology.Algebra.InfiniteSum.Real
import OAI.NumberTheory.Ostmann.ZeroDensity.SmoothZeroTermBounds

namespace OAI

/-! # The complete high-zero tail over a finite character family -/

namespace Ostmann
open scoped Classical BigOperators

theorem high_smooth_zero_tsum_bound {Z : ∀ χ, ComplexZeroEnumeration χ}
    (P : PublishedSmoothExplicitFormula Z) (Q : ℕ) (hQ : 1 ≤ Q)
    (F : Finset PrimitiveComplexCharacter) (hF : ∀ χ ∈ F, χ.modulus ≤ Q)
    (T X : ℝ) (hT : 0 ≤ T) (hX : 1 ≤ X) :
    (∑ χ ∈ F, ∑' i : ℕ, if T ≤ |((Z χ).zeros i).im| then
      ‖smoothZeroTerm Z χ X i‖ else 0) ≤
      (X * P.mellinConstant) *
        (2 * (2 * (P.zeroCountConstant * (Q : ℝ) ^ 2) * (Real.log Q + 3)) ^ 2 *
          Real.exp (-4 * Real.log (1 + T))) := by
  let f : (Σ _χ : PrimitiveComplexCharacter, ℕ) → ℝ := fun z =>
    if z.1 ∈ F ∧ T ≤ |((Z z.1).zeros z.2).im| then ‖smoothZeroTerm Z z.1 X z.2‖ else 0
  have hf : 0 ≤ f := by intro z; dsimp [f]; split_ifs <;> positivity
  have hb (S : Finset (Σ _χ : PrimitiveComplexCharacter, ℕ)) :
      (∑ z ∈ S, f z) ≤
        (X * P.mellinConstant) *
          (2 * (2 * (P.zeroCountConstant * (Q : ℝ) ^ 2) * (Real.log Q + 3)) ^ 2 *
            Real.exp (-4 * Real.log (1 + T))) := by
    let G := S.filter (fun z => z.1 ∈ F ∧ T ≤ |((Z z.1).zeros z.2).im|)
    have he : (∑ z ∈ S, f z) = ∑ z ∈ G, ‖smoothZeroTerm Z z.1 X z.2‖ := by
      simp only [G, Finset.sum_filter, f]
    rw [he]
    exact finite_high_smooth_zero_bound P Q hQ F hF G
      (fun z hz => (Finset.mem_filter.mp hz).2.1) T X hT hX
      (fun z hz => (Finset.mem_filter.mp hz).2.2)
  have hsum := summable_of_sum_le hf hb
  have hbound := Real.tsum_le_of_sum_le hf hb
  rw [hsum.tsum_sigma] at hbound
  have houter : (∑' χ, ∑' i, f ⟨χ, i⟩) = ∑ χ ∈ F, ∑' i, f ⟨χ, i⟩ := by
    apply tsum_eq_sum
    intro χ hχ
    simp only [f, hχ, false_and, ite_false, tsum_zero]
  rw [houter] at hbound
  convert hbound using 1
  apply Finset.sum_congr rfl
  intro χ hχ
  apply tsum_congr
  intro i
  simp only [f, hχ, true_and]

end Ostmann

end OAI
