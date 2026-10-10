import OAI.NumberTheory.CubicMoment.Decomposition.StoppedDivisorScale

namespace OAI

/-! A fixed power margin in the unrestricted large-divisor terms for
frequency length at most the three-fifths power of the coefficient length. -/
noncomputable section
namespace CubicFirstMoment

lemma stopped_frequency_monomial {b B a c d : ℝ}
    (hb : 1 ≤ b) (hB : 0 < B) (hBb : B ≤ b^(3/5:ℝ))
    (ha : (1/3:ℝ) ≤ a) (hexp : (a-1/3)*(3/5)+c ≤ d) :
    B^a*b^c ≤ B^(1/3:ℝ)*b^d := by
  have hbp : 0 < b := zero_lt_one.trans_le hb
  have hpower : B^(a-1/3) ≤ b^((a-1/3)*(3/5)) := by
    apply (Real.rpow_le_rpow hB.le hBb (by linarith)).trans_eq
    rw [←Real.rpow_mul hbp.le]
    congr 1
    ring
  calc
    _ = B^(1/3:ℝ)*(B^(a-1/3)*b^c) := by
      rw [←mul_assoc,←Real.rpow_add hB]
      congr 2
      ring
    _ ≤ B^(1/3:ℝ)*(b^((a-1/3)*(3/5))*b^c) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpower (by positivity)) (by positivity)
    _ = B^(1/3:ℝ)*b^((a-1/3)*(3/5)+c) := by rw [Real.rpow_add hbp]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hb hexp) (by positivity)

theorem stopped_large_divisor_power {b B C₁ C₂ C₃ : ℝ}
    (hb : 1 ≤ b) (hB : 0 < B) (hBb : B ≤ b^(3/5:ℝ))
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃) :
    (2*B*b)^(1/1000:ℝ)*(
      B*b*b^(1/12:ℝ)*C₁+B^(2/3:ℝ)*b^(5/3:ℝ)*C₂+
      B^(1/3:ℝ)*b^2*(b^(1/8:ℝ))^(-(1/2:ℝ))*C₃) ≤
      (2:ℝ)^(1/1000:ℝ)*(C₁+C₂+C₃)*B^(1/3:ℝ)*b^(2-1/20:ℝ) := by
  have hbp : 0 < b := zero_lt_one.trans_le hb
  have h₁ := stopped_frequency_monomial hb hB hBb
    (show (1/3:ℝ) ≤ 1+1/1000 by norm_num)
    (show ((1+1/1000:ℝ)-1/3)*(3/5)+(1+1/12+1/1000) ≤ 2-1/20 by norm_num)
  have h₂ := stopped_frequency_monomial hb hB hBb
    (show (1/3:ℝ) ≤ 2/3+1/1000 by norm_num)
    (show ((2/3+1/1000:ℝ)-1/3)*(3/5)+(5/3+1/1000) ≤ 2-1/20 by norm_num)
  have h₃ := stopped_frequency_monomial hb hB hBb
    (show (1/3:ℝ) ≤ 1/3+1/1000 by norm_num)
    (show ((1/3+1/1000:ℝ)-1/3)*(3/5)+(2+(-(1/16))+1/1000) ≤ 2-1/20 by norm_num)
  have hs : (b^(1/8:ℝ))^(-(1/2:ℝ)) = b^(-(1/16:ℝ)) := by
    rw [←Real.rpow_mul hbp.le]
    norm_num
  have hp : (2*B*b)^(1/1000:ℝ) = (2:ℝ)^(1/1000:ℝ)*B^(1/1000:ℝ)*b^(1/1000:ℝ) := by
    rw [Real.mul_rpow (by positivity : 0 ≤ 2*B) hbp.le,
      Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hB.le]
  calc
    _ = (2:ℝ)^(1/1000:ℝ)*(
        C₁*(B^(1+1/1000:ℝ)*b^(1+1/12+1/1000:ℝ))+
        C₂*(B^(2/3+1/1000:ℝ)*b^(5/3+1/1000:ℝ))+
        C₃*(B^(1/3+1/1000:ℝ)*b^(2+(-(1/16))+1/1000:ℝ))) := by
      rw [hp,hs]
      simp only [Real.rpow_add hB,Real.rpow_add hbp,Real.rpow_one,Real.rpow_two]
      ring
    _ ≤ (2:ℝ)^(1/1000:ℝ)*(
        C₁*(B^(1/3:ℝ)*b^(2-1/20:ℝ))+C₂*(B^(1/3:ℝ)*b^(2-1/20:ℝ))+
        C₃*(B^(1/3:ℝ)*b^(2-1/20:ℝ))) := by
      exact mul_le_mul_of_nonneg_left (add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left h₁ hC₁) (mul_le_mul_of_nonneg_left h₂ hC₂))
        (mul_le_mul_of_nonneg_left h₃ hC₃)) (by positivity)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
