import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Sphere.SphereAmbient

namespace OAI

/-! Quantitative estimates for the distance-set construction. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4FullFar
open Real

lemma far_scaled_lengthND (v b d : ℝ) (hd : (2:ℝ)^(-b)/4≤d) :
    (2:ℝ)^(v-b)/4≤(2:ℝ)^v*d := by
  calc
    _ = (2:ℝ)^v*((2:ℝ)^(-b)/4) := by
      rw [← mul_div_assoc,← Real.rpow_add (by norm_num : (0:ℝ)<2)]
      rfl
    _ ≤ _ := mul_le_mul_of_nonneg_left hd (by positivity)

lemma far_stationary_gainND (n : ℕ) (v b : ℝ) {Λ Μ : ℝ}
    (hΛ : (2:ℝ)^(v-b)/4≤Λ) (hΜ : (2:ℝ)^(v-b)/4≤Μ) :
    Λ^(-(n:ℝ)/2)*Μ^(-(n:ℝ)/2) ≤ (4:ℝ)^n*(2:ℝ)^(-(n:ℝ)*(v-b)) := by
  have hp : 0<(2:ℝ)^(v-b)/4 := by positivity
  have hn : -(n:ℝ)/2≤0 := by have hh := Nat.cast_nonneg (α := ℝ) n; linarith
  calc
    _ ≤ ((2:ℝ)^(v-b)/4)^(-(n:ℝ)/2)*((2:ℝ)^(v-b)/4)^(-(n:ℝ)/2) := by
      apply mul_le_mul (Real.rpow_le_rpow_of_nonpos hp hΛ hn)
        (Real.rpow_le_rpow_of_nonpos hp hΜ hn)
        (Real.rpow_nonneg (hp.le.trans hΜ) _) (Real.rpow_nonneg hp.le _)
    _ = ((2:ℝ)^(v-b)/4)^(-(n:ℝ)) := by
      rw [← Real.rpow_add hp]
      congr 1
      ring
    _ = (4:ℝ)^n*(2:ℝ)^(-(n:ℝ)*(v-b)) := by
      rw [Real.div_rpow (by positivity : (0:ℝ)≤(2:ℝ)^(v-b)) (by norm_num),
        ← Real.rpow_mul (by norm_num : (0:ℝ)≤2),Real.rpow_neg (by norm_num : (0:ℝ)≤4),
        Real.rpow_natCast,div_inv_eq_mul]
      rw [mul_comm]
      congr 2
      ring

theorem far_original_length_kernelND (n : ℕ) (v b d₁ d₂ H : ℝ) (hH : 0≤H)
    (hd₁ : (2:ℝ)^(-b)/4≤d₁) (hd₂ : (2:ℝ)^(-b)/4≤d₂) :
    H*(((2:ℝ)^v*d₁)^(-(n:ℝ)/2)*((2:ℝ)^v*d₂)^(-(n:ℝ)/2))/
        (1+|(2:ℝ)^v*d₁-(2:ℝ)^v*d₂|)^2 ≤
      (H*4^n)*(2:ℝ)^(-(n:ℝ)*(v-b))/(1+(2:ℝ)^v*|d₁-d₂|)^2 := by
  rw [← mul_sub,abs_mul,abs_of_pos (Real.rpow_pos_of_pos (by norm_num) v)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hh := mul_le_mul_of_nonneg_left (far_stationary_gainND n v b
    (far_scaled_lengthND v b d₁ hd₁) (far_scaled_lengthND v b d₂ hd₂)) hH
  simpa only [mul_assoc] using hh

end Attempt4FullFar
end GraphLiteralSupport
end
end

end OAI
