import OAI.Geometry.NodalSets.Elliptic.NormalizedJetBounds

namespace OAI

namespace Yau.Geometry
open Yau.Jets
open scoped ContDiff
noncomputable section

lemma normalizedRealJet_polynomial_derivative_bound (f S : Coord → ℝ)
    (hf : ContDiff ℝ ∞ f) (hS : ContDiff ℝ ∞ S) (x : Coord)
    {N A B H : ℝ} (hN : 1 ≤ N) (hA : 0 ≤ A) (hB : 0 ≤ B) (hH : 0 ≤ H)
    (hs : ‖fderiv ℝ S x‖ ≤ A)
    (hf0 : |f x| ≤ B*N^3*H) (hf1 : ‖fderiv ℝ f x‖ ≤ B*N^4*H)
    (hf2 : ‖iteratedFDeriv ℝ 2 f x‖ ≤ B*N^5*H) :
    ‖fderiv ℝ (fun z ↦ normalizedRealJet f N (S z) z) x‖ ≤
      (6*(A+1)*B)*N^4*H*Real.exp (-N*S x) := by
  have hNp : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have h0 : max |f x| (N⁻¹*‖fderiv ℝ f x‖) ≤ B*N^3*H := by
    refine max_le hf0 ?_
    calc
      _ ≤ N⁻¹*(B*N^4*H) := mul_le_mul_of_nonneg_left hf1 (by positivity)
      _ = B*N^3*H := by field_simp
  have h1 : max ‖fderiv ℝ f x‖ (N⁻¹*‖iteratedFDeriv ℝ 2 f x‖) ≤ B*N^4*H := by
    refine max_le hf1 ?_
    calc
      _ ≤ N⁻¹*(B*N^5*H) := mul_le_mul_of_nonneg_left hf2 (by positivity)
      _ = B*N^4*H := by field_simp
  calc
    _ ≤ 6*Real.exp (-N*S x)*(N*‖fderiv ℝ S x‖*
        max |f x| (N⁻¹*‖fderiv ℝ f x‖)+
        max ‖fderiv ℝ f x‖ (N⁻¹*‖iteratedFDeriv ℝ 2 f x‖)) :=
      normalizedRealJet_fderiv_le f S hf hS x hNp.le
    _ ≤ 6*Real.exp (-N*S x)*(N*A*(B*N^3*H)+B*N^4*H) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply add_le_add _ h1
      calc
        _ ≤ N*‖fderiv ℝ S x‖*(B*N^3*H) :=
          mul_le_mul_of_nonneg_left h0 (mul_nonneg hNp.le (norm_nonneg _))
        _ ≤ N*A*(B*N^3*H) :=
          mul_le_mul_of_nonneg_right
            (by simpa only [mul_comm] using mul_le_mul hs (le_refl N) hNp.le hA)
            (mul_nonneg (mul_nonneg hB (pow_nonneg hNp.le _)) hH)
    _ = _ := by ring

end
end Yau.Geometry

end OAI
