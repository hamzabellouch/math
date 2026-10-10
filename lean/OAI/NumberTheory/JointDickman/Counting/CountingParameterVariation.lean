import OAI.NumberTheory.JointDickman.Counting.CountingCoefficientRegularity

namespace OAI

/-! # Uniform parameter variation of the finite counting kernel -/
namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem countingPrimeKernel_parameter_variation
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (P : MvPolynomial (Fin 4) ℝ) (m : (Fin 4 →₀ ℕ) → ℕ) (hm : ∀ d, 0 < m d)
    (c : (Fin 4 →₀ ℕ) → ℕ → ℝ) (hc : ∀ d, c d 0 = squarefreeLeadingConstant (1/2))
    (D : (Fin 4 →₀ ℕ) → ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ B : ℕ in atTop, ∀ (j : ℕ) (T σ σ' : ℝ),
      1 ≤ T → Real.log T ≤ (B : ℝ)/10 → η*T ≤ j → |σ| ≤ 3 → |σ'| ≤ 3 →
      ∀ x y, |countingPrimeKernel P m B j c D T σ x y-
        countingPrimeKernel P m B j c D T σ' x y| ≤ K*|σ-σ'| := by
  choose C hC hbound using fun d =>
    countingTermCoefficient_regular hM hMP P d (hm d) (c d) (hc d) (D d) hη
  let K := ∑ d ∈ P.support, (m d : ℝ)^2*C d/(channelMesh (m d))^2
  refine ⟨K,by dsimp [K]; exact sum_nonneg (fun d _ => div_nonneg (mul_nonneg (sq_nonneg _) (hC d)) (sq_nonneg _)),?_⟩
  filter_upwards [(eventually_all_finset P.support).mpr (fun d _ => hbound d)] with B hB
  intro j T σ σ' hT hlog hj hσ hσ' x y
  simp only [countingPrimeKernel_coefficients,← sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ d ∈ P.support, (m d : ℝ)^2*C d/(channelMesh (m d))^2*|σ-σ'| := by
      apply sum_le_sum
      intro d hd
      apply (abs_sum_le_sum_abs _ _).trans
      calc
        _ ≤ ∑ a : Fin (m d), ∑ b : Fin (m d), C d*|σ-σ'|/(channelMesh (m d))^2 := by
          apply sum_le_sum
          intro a _
          apply (abs_sum_le_sum_abs _ _).trans
          apply sum_le_sum
          intro b _
          have hmesh := channelMesh_pos (hm d)
          have hCd := hC d
          have hh := hB d hd j j T σ σ' hT hlog hj hj hσ hσ' a b
          simp only [sub_self,abs_zero,zero_div,zero_add] at hh
          rw [← sub_mul,← sub_mul,abs_mul,abs_mul]
          have hx := primeCoarseFeature_bounds (hm d) a x
          have hy := primeCoarseFeature_bounds (hm d) b y
          rw [abs_of_nonneg hx.1,abs_of_nonneg hy.1]
          have hprod := mul_le_mul
            (mul_le_mul hh hx.2 hx.1 (mul_nonneg (hC d) (abs_nonneg _)))
            hy.2 hy.1 (by positivity : 0 ≤ C d*|σ-σ'| *(1/channelMesh (m d)))
          exact hprod.trans_eq (by ring)
        _ = _ := by simp; ring
    _ = K*|σ-σ'| := by rw [sum_mul]

end JointDickman

end OAI
