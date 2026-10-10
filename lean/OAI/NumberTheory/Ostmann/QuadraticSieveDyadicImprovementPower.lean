import OAI.NumberTheory.Ostmann.QuadraticSieveDyadicImprovementScale

namespace OAI

noncomputable section
namespace Ostmann.QuadraticSieve

theorem inflated_dyadic_product_le {M N X Y B δ : ℝ}
    (hM : 1 ≤ M) (hN : 1 ≤ N) (hX : X ≤ N^2) (hB : 0 ≤ B)
    (_hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hY : Y ≤ B*(M*N)^δ*(M+X)) : Y*N ≤ 2*B*(M*N)^4 := by
  have hM0 : 0 ≤ M := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hP : 1 ≤ M*N := one_le_mul_of_one_le_of_one_le hM hN
  have hMP : M ≤ M*N := le_mul_of_one_le_right hM0 hN
  have hNP : N ≤ M*N := le_mul_of_one_le_left hN0 hM
  have hpow : (M*N)^δ ≤ M*N := by
    simpa using Real.rpow_le_rpow_of_exponent_le hP hδ1
  have hM2 : M ≤ (M*N)^2 := by nlinarith
  have hX2 : X ≤ (M*N)^2 := hX.trans (pow_le_pow_left₀ hN0 hNP 2)
  have hsum : M+X ≤ 2*(M*N)^2 := by linarith
  calc
    Y*N ≤ (B*(M*N)^δ*(M+X))*N := mul_le_mul_of_nonneg_right hY hN0
    _ ≤ (B*(M*N)^δ*(2*(M*N)^2))*N := by gcongr
    _ ≤ (B*(M*N)*(2*(M*N)^2))*(M*N) := by gcongr
    _ = _ := by ring

theorem inflated_dyadic_sum_le {M N X Y B δ : ℝ}
    (hM : 1 ≤ M) (hN : 1 ≤ N) (hX : 0 ≤ X) (hδ : 0 ≤ δ)
    (hY : Y ≤ B*(M*N)^δ*(M+X)) : Y+X ≤ (B+1)*(M*N)^δ*(M+X) := by
  have hP : 1 ≤ M*N := one_le_mul_of_one_le_of_one_le hM hN
  have hp : 1 ≤ (M*N)^δ := Real.one_le_rpow hP hδ
  have hb : X ≤ (M*N)^δ*(M+X) := by
    have hsum : 0 ≤ M+X := by linarith
    have hh := mul_le_mul_of_nonneg_right hp hsum
    nlinarith
  nlinarith

end Ostmann.QuadraticSieve

end

end OAI
