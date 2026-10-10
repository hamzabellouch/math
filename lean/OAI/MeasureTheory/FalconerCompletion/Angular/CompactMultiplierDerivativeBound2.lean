import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Angular.CompactContDiffOnDerivativeBound3

namespace OAI

/-! Angular cutoffs and derivative estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell
open Set Metric
open scoped ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma compact_multiplier_derivative_bound {w : E → ℂ} {K : Set E}
    (hK : IsCompact K) (hw : ContDiff ℝ ∞ w) (m : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (b : E → ℂ) (A : ℝ), ContDiff ℝ ∞ b → 1 ≤ A →
      (∀ j ≤ m, ∀ x ∈ K, ‖iteratedFDeriv ℝ j b x‖ ≤ C*A^j) →
      ∀ j ≤ m, ∀ x ∈ K, ‖iteratedFDeriv ℝ j (fun x => w x*b x) x‖ ≤ D*A^j := by
  obtain ⟨W,hW,hWw⟩ := compact_contDiffOn_derivative_bound isOpen_univ hK
    (subset_univ K) hw.contDiffOn m
  have hW0 : 0 ≤ W := zero_le_one.trans hW
  refine ⟨2^m*W*C,by positivity,?_⟩
  intro b A hb hA hderiv j hj x hx
  have hA0 := zero_le_one.trans hA
  have hi : (j : WithTop ℕ∞) ≤ (↑(⊤:ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast (le_top : (j:ℕ∞) ≤ ⊤)
  apply (norm_iteratedFDeriv_mul_le hw hb x hi).trans
  have hsum : (∑ i ∈ Finset.range (j+1), (j.choose i:ℝ)) = 2^j := by
    exact_mod_cast Nat.sum_range_choose j
  calc
    (∑ i ∈ Finset.range (j+1), (j.choose i:ℝ)*‖iteratedFDeriv ℝ i w x‖*
      ‖iteratedFDeriv ℝ (j-i) b x‖) ≤
        ∑ i ∈ Finset.range (j+1), (j.choose i:ℝ)*W*(C*A^j) := by
      apply Finset.sum_le_sum
      intro i hi
      have hij : i ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have hw' : ‖iteratedFDeriv ℝ i w x‖ ≤ W := by
        simpa only [iteratedFDerivWithin_univ] using hWw i (hij.trans hj) x hx
      apply mul_le_mul
        (mul_le_mul_of_nonneg_left hw' (by positivity))
        ((hderiv (j-i) ((Nat.sub_le _ _).trans hj) x hx).trans
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hA (Nat.sub_le _ _)) hC))
        (norm_nonneg _) (by positivity)
    _ = 2^j*W*(C*A^j) := by rw [← Finset.sum_mul,← Finset.sum_mul,hsum]
    _ ≤ 2^m*W*(C*A^j) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hj) hW0)
      (by positivity)
    _ = _ := by ring

end Attempt4PrefixShell
end GraphLiteralSupport
end
end

end OAI
