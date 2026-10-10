import OAI.Analysis.LipschitzHilbert.Trees.ResidualBudget

namespace OAI

/-! The fixed polynomial residual losses are absorbed by the source
mass cutoff, uniformly for the full permitted range of the phase exponent. -/

noncomputable section
namespace LipschitzHilbert

theorem source_principal_residual_costs {L Cmarked Cunary A_M μ C₁ C₂ : ℝ}
    (hL : 1 ≤ L) (hC₁ : C₁ ≤ L) (hC₂ : C₂ ≤ L) (hAM : 0 ≤ A_M)
    (hchoice : 4*(max Cmarked Cunary+3/2) ≤ A_M) (hμ : μ ≤ 1/12) :
    Real.sqrt L*C₁*L^Cmarked*(L^A_M)^(-(1/2:ℝ)+μ)+
      Real.sqrt L*C₂*L^Cunary*(L^A_M)^(-(1/3:ℝ)+μ) ≤ 2 := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hbudget := residual_polynomial_budget (C := max Cmarked Cunary+1)
    hL hμ hAM (by linarith)
  have hcoeff (C b : ℝ) (hC : C ≤ L) (hb : b ≤ max Cmarked Cunary) :
      C*L^b ≤ L^(max Cmarked Cunary+1) := by
    calc
      _ ≤ L*L^b := mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hL0.le _)
      _ ≤ L*L^(max Cmarked Cunary) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hL hb) hL0.le
      _ = _ := by rw [Real.rpow_add hL0,Real.rpow_one]; ring
  have hmarked : Real.sqrt L*C₁*L^Cmarked*(L^A_M)^(-(1/2:ℝ)+μ) ≤ 1 := by
    calc
      _ = L^(1/2:ℝ)*(C₁*L^Cmarked)*(L^A_M)^(-(1/2:ℝ)+μ) := by
        rw [Real.sqrt_eq_rpow]; ring
      _ ≤ L^(1/2:ℝ)*L^(max Cmarked Cunary+1)*(L^A_M)^(-(1/2:ℝ)+μ) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hcoeff C₁ Cmarked hC₁ (le_max_left _ _))
            (Real.rpow_nonneg hL0.le _)) (Real.rpow_nonneg (Real.rpow_nonneg hL0.le _) _)
      _ ≤ 1 := hbudget.2
  have hunary : Real.sqrt L*C₂*L^Cunary*(L^A_M)^(-(1/3:ℝ)+μ) ≤ 1 := by
    calc
      _ = L^(1/2:ℝ)*(C₂*L^Cunary)*(L^A_M)^(-(1/3:ℝ)+μ) := by
        rw [Real.sqrt_eq_rpow]; ring
      _ ≤ L^(1/2:ℝ)*L^(max Cmarked Cunary+1)*(L^A_M)^(-(1/3:ℝ)+μ) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hcoeff C₂ Cunary hC₂ (le_max_right _ _))
            (Real.rpow_nonneg hL0.le _)) (Real.rpow_nonneg (Real.rpow_nonneg hL0.le _) _)
      _ ≤ 1 := hbudget.1
  linarith

end LipschitzHilbert

end

end OAI
