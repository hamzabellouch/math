import OAI.NumberTheory.Ostmann.Arithmetic.PrimeCellMeshCounts

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.PrimeCellMeshBudget
open ScaleBudget Filter

def bulkCostConstant (k : ℕ) (C : ℝ) : ℝ :=
  (|C|+1)*(Conclusion.bulkScale k+1)

lemma bulkCostConstant_pos (k : ℕ) (C : ℝ) : 0 < bulkCostConstant k C := by
  unfold bulkCostConstant Conclusion.bulkScale
  positivity

theorem actual_bulk_cost_le (k : ℕ) (C : ℝ) {L : ℝ} (hL : 1 ≤ L) :
    C*((Conclusion.bulkSize k L:ℝ)+1) ≤ bulkCostConstant k C*L := by
  have hm := (Conclusion.bulkSize_bounds k (by linarith : 0 ≤ L)).2
  have hsize : (Conclusion.bulkSize k L:ℝ)+1 ≤ (Conclusion.bulkScale k+1)*L := by nlinarith
  calc
    _ ≤ (|C|+1)*((Conclusion.bulkSize k L:ℝ)+1) :=
      mul_le_mul_of_nonneg_right (by linarith [le_abs_self C]) (by positivity)
    _ ≤ (|C|+1)*((Conclusion.bulkScale k+1)*L) :=
      mul_le_mul_of_nonneg_left hsize (by positivity)
    _ = _ := by unfold bulkCostConstant; ring

theorem variation_cost_le (k : ℕ) (C : ℝ) {L σ : ℝ}
    (hL : 1 ≤ L) (hσ : 0 ≤ σ) :
    C*((Conclusion.bulkSize k L:ℝ)+1)*Real.exp (σ*L)+C*((Conclusion.bulkSize k L:ℝ)+1) ≤
      (2*bulkCostConstant k C)*L*Real.exp (σ*L) := by
  have hc := actual_bulk_cost_le k C hL
  have he : 1 ≤ Real.exp (σ*L) := Real.one_le_exp (mul_nonneg hσ (by linarith))
  have h1 := mul_le_mul_of_nonneg_right hc (Real.exp_nonneg (σ*L))
  have h2 := mul_le_mul_of_nonneg_left he
    (mul_nonneg (bulkCostConstant_pos k C).le (by linarith : 0 ≤ L))
  nlinarith

theorem joint_error_cost_le (r : Row) (k : ℕ) (C : ℝ) {L σ : ℝ}
    (hL : 1 ≤ L) (hσ : σ ≤ r.δ) :
    C*((Conclusion.bulkSize k L:ℝ)+1)*
        (Real.exp (r.δ*L)+L+Real.exp (r.μ*L)+Real.exp (σ*L)) ≤
      (4*bulkCostConstant k C)*L^2*Real.exp (r.δ*L) := by
  have hLn : 0 ≤ L := by linarith
  have hd : 0 ≤ r.δ := by linarith [r.μ_pos,r.μ_lt_δ]
  have he : 1 ≤ Real.exp (r.δ*L) := Real.one_le_exp (mul_nonneg hd hLn)
  have heμ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right r.μ_lt_δ.le hLn)
  have heσ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hσ hLn)
  have hEL := mul_le_mul_of_nonneg_right hL (Real.exp_nonneg (r.δ*L))
  have hLE := mul_le_mul_of_nonneg_left he hLn
  have hbracket : Real.exp (r.δ*L)+L+Real.exp (r.μ*L)+Real.exp (σ*L) ≤
      4*L*Real.exp (r.δ*L) := by nlinarith
  have hc := actual_bulk_cost_le k C hL
  have hmain := mul_le_mul hc hbracket
    (by positivity : 0 ≤ Real.exp (r.δ*L)+L+Real.exp (r.μ*L)+Real.exp (σ*L))
    (mul_nonneg (bulkCostConstant_pos k C).le hLn)
  convert hmain using 1
  ring

end Ostmann.Arithmetic.PrimeCellMeshBudget

end

end OAI
