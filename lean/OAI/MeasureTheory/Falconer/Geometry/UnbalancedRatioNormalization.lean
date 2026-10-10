import OAI.MeasureTheory.Falconer.Geometry.CommonNormalizedProjections

namespace OAI

/-! Normalization of common ratio counts when the two original coordinate
sets have comparable, rather than identical, cardinalities. -/
namespace Falconer

 theorem normalize_unbalanced_ratio {D C K ρ N P Q A : ℝ}
    (hC : 0 ≤ C) (hρ : 0 < ρ) (hN : 0 < N) (hP : 0 < P)
    (hNP : N ≤ Q*P) (hA : ρ*N ≤ A)
    (hbound : D*ρ^12*N*P^2 ≤ C*(K*N)^4) :
    D ≤ (C*K^4*Q^2/ρ^13)*A := by
  have hNP2 : N^2 ≤ Q^2*P^2 := by
    have hh := pow_le_pow_left₀ hN.le hNP 2
    nlinarith
  have hcore : D*ρ^12 ≤ C*K^4*N*Q^2 := by
    apply (mul_le_mul_iff_left₀ (mul_pos hN (sq_pos_of_pos hP))).1
    calc
      _ = D*ρ^12*N*P^2 := by ring
      _ ≤ C*(K*N)^4 := hbound
      _ = (C*K^4*N^2)*N^2 := by ring
      _ ≤ (C*K^4*N^2)*(Q^2*P^2) :=
        mul_le_mul_of_nonneg_left hNP2 (by positivity)
      _ = _ := by ring
  have hd : D ≤ (C*K^4*Q^2/ρ^12)*N := by
    have hh := (le_div_iff₀ (pow_pos hρ 12)).2 hcore
    convert hh using 1; ring
  have hs := mul_le_mul_of_nonneg_left hA (show 0 ≤ C*K^4*Q^2/ρ^13 by positivity)
  calc
    _ ≤ (C*K^4*Q^2/ρ^12)*N := hd
    _ = (C*K^4*Q^2/ρ^13)*(ρ*N) := by field_simp
    _ ≤ _ := hs

end Falconer

end OAI
