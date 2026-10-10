import OAI.Analysis.LipschitzHilbert.Estimates.PopularTopMask

namespace OAI

/-! Normalize the weak-L2 mask error by the source relation between
total top area and the two testing measures. -/

noncomputable section
namespace LipschitzHilbert

theorem sqrt_area_product (L s N F G S : ℝ) (hL : 0 < L) (hN : 0 ≤ N)
    (hF : 0 ≤ F) (hGle : G ≤ F) (hS : S ≤ L^s*N^2*F) :
    Real.sqrt S*Real.sqrt G ≤ L^(s/2)*N*F := by
  have hroot : Real.sqrt (L^s) = L^(s/2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hL.le]
    congr 1
    ring
  calc
    _ ≤ Real.sqrt (L^s*N^2*F)*Real.sqrt F :=
      mul_le_mul (Real.sqrt_le_sqrt hS) (Real.sqrt_le_sqrt hGle)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = L^(s/2)*N*F := by
      rw [Real.sqrt_mul (by positivity : 0 ≤ L^s*N^2),
        Real.sqrt_mul (Real.rpow_nonneg hL.le _), Real.sqrt_sq hN, hroot]
      calc
        _ = L^(s/2)*N*(Real.sqrt F*Real.sqrt F) := by ring
        _ = _ := by rw [Real.mul_self_sqrt hF]

theorem mask_error_normalization (L C e s H N F G S : ℝ)
    (hL : 0 < L) (hC : 0 ≤ C) (hCL : 2*C ≤ L^2) (hN : 0 ≤ N)
    (hF : 0 ≤ F) (hGle : G ≤ F) (hS : S ≤ L^s*N^2*F) :
    2*L^(-(H+e+s/2+2))*(C*L^e*Real.sqrt S)*Real.sqrt G ≤ L^(-H)*N*F := by
  have harea := sqrt_area_product L s N F G S hL hN hF hGle hS
  have hpower : L^(-(H+e+s/2+2))*L^e*L^(s/2) = L^(-H-2) := by
    rw [← Real.rpow_add hL, ← Real.rpow_add hL]
    congr 1
    ring
  have hpower2 : L^2*L^(-H-2) = L^(-H) := by
    rw [← Real.rpow_two L, ← Real.rpow_add hL]
    congr 1
    ring
  calc
    _ = (2*C*L^(-(H+e+s/2+2))*L^e)*(Real.sqrt S*Real.sqrt G) := by ring
    _ ≤ (2*C*L^(-(H+e+s/2+2))*L^e)*(L^(s/2)*N*F) :=
      mul_le_mul_of_nonneg_left harea (by positivity)
    _ = (2*C*L^(-H-2))*(N*F) := by
      rw [show (2*C*L^(-(H+e+s/2+2))*L^e)*(L^(s/2)*N*F) =
        (2*C)*(L^(-(H+e+s/2+2))*L^e*L^(s/2))*(N*F) by ring, hpower]
    _ ≤ (L^2*L^(-H-2))*(N*F) := by gcongr
    _ = L^(-H)*N*F := by rw [hpower2]; ring

end LipschitzHilbert

end

end OAI
