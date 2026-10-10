import Mathlib
import OAI.Analysis.LaughlinGap.FourComparison
import OAI.Analysis.LaughlinGap.RationalCoupling

namespace OAI

/-! Rational Four Coefficients. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators
open Spin

def vCoefficient (D T r p j k : ℕ) : ℚ :=
  if D ≤ T ∧ r ≤ j+k ∧ p+j+k=T then
    uCoefficient 1 r (j+k) j * uCoefficient 1 (D-r) (T-r) p else 0

noncomputable def copyNormalization (D r : ℕ) : ℝ :=
  1/(rootFactorial r*rootFactorial (D-r))

lemma two_pow_odd_sqrt {r : ℕ} (hr : Odd r) :
    (2:ℝ)^((r+1)/2) = Real.sqrt 2 ^ (r+1) := by
  have he : 2*((r+1)/2) = r+1 := by obtain ⟨k,hk⟩ := hr; omega
  calc
    (2:ℝ)^((r+1)/2) = (Real.sqrt 2 ^ 2)^((r+1)/2) := by
      rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    _ = Real.sqrt 2^(r+1) := by rw [← pow_mul,he]

lemma coupling_exponent_identity {p j k T r : ℕ} (ht : p+j+k=T) (hr : r ≤ j+k)
    (ho : Odd r) :
    Real.sqrt 2 * (2:ℝ)^T = (2:ℝ)^((r+1)/2) * Real.sqrt 2 ^ p *
      Real.sqrt 2 ^ (j+k) * Real.sqrt 2 ^ (T-r) := by
  rw [two_pow_odd_sqrt ho]
  have hpow : (2:ℝ)^T = Real.sqrt 2^(2*T) := by
    rw [pow_mul,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  rw [hpow,← pow_add,← pow_add,← pow_add,← pow_succ']
  congr 1
  omega

lemma fourWeightCoefficientStar_rational {D r : ℕ} (hD : r ≤ D) (ho : Odd r)
    (T p j k : ℕ) :
    fourWeightCoefficientStar D T r p j k =
      (vCoefficient D T r p j k : ℝ) * (2:ℝ)^((r+1)/2) * Real.sqrt 2 ^ p *
        rootFactorial p * rootFactorial j * rootFactorial k * copyNormalization D r /
        ((2:ℝ)^T * rootFactorial (T-D)) := by
  by_cases hT : D ≤ T
  · by_cases ht : r ≤ j+k ∧ p+j+k=T
    · have hr : D-r ≤ T-r := Nat.sub_le_sub_right hT r
      have he₁ : j+k-j=k := by omega
      have he₂ : T-r-p=j+k-r := by omega
      have he₃ : T-r-(D-r)=T-D := by omega
      rw [fourWeightCoefficientStar,ite_eq_left hT,fourBodyCoefficientStar,ite_eq_left ht,
        balancedCouplingCoefficient_rational ht.1,balancedCouplingCoefficient_rational hr,
        he₁,he₂,he₃,vCoefficient,ite_eq_left ⟨hT,ht.1,ht.2⟩]
      push_cast
      unfold copyNormalization
      have he := coupling_exponent_identity ht.2 ht.1 ho
      field_simp [rootFactorial_ne_zero,
        Real.sqrt_ne_zero'.mpr (by norm_num : (0:ℝ) < 2)]
      linear_combination
        (uCoefficient 1 r (j+k) j : ℝ) * (uCoefficient 1 (D-r) (T-r) p : ℝ) * he
    · simp only [fourWeightCoefficientStar,ite_eq_left hT,fourBodyCoefficientStar,ite_eq_right ht]
      have hn : ¬ (D ≤ T ∧ r ≤ j+k ∧ p+j+k=T) := by tauto
      simp only [vCoefficient,ite_eq_right hn,Rat.cast_zero,zero_mul,zero_div]
  · have hn : ¬ (D ≤ T ∧ r ≤ j+k ∧ p+j+k=T) := by tauto
    simp [fourWeightCoefficientStar,hT,vCoefficient]

end LaughlinGap.RealOccupation

end

end OAI
