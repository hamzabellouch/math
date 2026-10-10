import OAI.NumberTheory.TwoPoint.Halasz.HalaszTorusBessel

namespace OAI

/-! Finite synthesis bounded by the number of overlapping localization
windows, retaining the actual pair count. -/
namespace TwoPointCorrelations

open Finset Complex
open scoped Classical ComplexConjugate

lemma halasz_synthesis_pair_sum {ι E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (S : Finset ι) (v : ι → E) (a : ι → ℂ)
    (ha : ∀ i∈S, ‖a i‖≤1) :
    ‖∑ i∈S,a i • v i‖^2≤∑ i∈S,∑ j∈S,‖inner ℂ (v i) (v j)‖ := by
  calc
    _ = (inner ℂ (∑ i∈S,a i • v i) (∑ i∈S,a i • v i)).re :=
      norm_sq_eq_re_inner (𝕜 := ℂ) _
    _ ≤ ‖inner ℂ (∑ i∈S,a i • v i) (∑ i∈S,a i • v i)‖ := re_le_norm _
    _ = ‖∑ i∈S,∑ j∈S,conj (a i)*a j*inner ℂ (v i) (v j)‖ := by
      simp only [sum_inner,inner_sum,inner_smul_left,inner_smul_right,mul_sum]
      rw [sum_comm]
      congr 1
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      ring
    _ ≤ ∑ i∈S,∑ j∈S,‖conj (a i)*a j*inner ℂ (v i) (v j)‖ :=
      (norm_sum_le _ _).trans (sum_le_sum (fun _ _ => norm_sum_le _ _))
    _ ≤ _ := by
      apply sum_le_sum
      intro i hi
      apply sum_le_sum
      intro j hj
      rw [norm_mul,norm_mul,norm_conj]
      have hmul : ‖a i‖*‖a j‖≤1 := by
        calc
          _ ≤ 1*1 := mul_le_mul (ha i hi) (ha j hj) (norm_nonneg _) zero_le_one
          _ = 1 := mul_one _
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hmul (norm_nonneg _)

theorem halasz_synthesis_overlap {ι E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (S : Finset ι) (v : ι → E) (a : ι → ℂ)
    (R : ι → ι → Prop) {V : ℝ} (ha : ∀ i∈S,‖a i‖≤1)
    (hR : ∀ i∈S,∀ j∈S,‖inner ℂ (v i) (v j)‖ ≤ (if R i j then V else 0)) :
    ‖∑ i∈S,a i • v i‖^2≤V*(((S×ˢS).filter (fun p => R p.1 p.2)).card:ℝ) := by
  apply (halasz_synthesis_pair_sum S v a ha).trans
  calc
    _ ≤ ∑ i∈S,∑ j∈S,if R i j then V else 0 :=
      sum_le_sum (fun i hi => sum_le_sum (fun j hj => hR i hi j hj))
    _ = _ := by
      rw [← sum_product S S (fun p : ι×ι => if R p.1 p.2 then V else 0)]
      simp only [card_eq_sum_ones,Nat.cast_sum,sum_filter]
      rw [mul_sum]
      apply sum_congr rfl
      intro p _
      by_cases h : R p.1 p.2 <;> simp [h]

end TwoPointCorrelations

end OAI
