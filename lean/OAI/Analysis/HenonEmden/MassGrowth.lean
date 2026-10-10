import OAI.Analysis.HenonEmden.ProductBounds

namespace OAI

section MassGrowth

open Set Filter Topology MeasureTheory
open scoped ContDiff
open Set Filter Topology
open scoped RealInnerProductSpace ContDiff
open Set Filter Topology
open scoped ContDiff
open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal
open Set Filter Topology MeasureTheory
open Set Filter Topology
open MeasureTheory
open scoped Convolution
open Set Filter Topology
open MeasureTheory Set Filter Topology
open scoped ContDiff
noncomputable section


namespace HenonLaneEmden
noncomputable def sourceConstant (n : ℕ) (p q A B : ℝ) : ℝ :=
  ((ballConstant n*weightMass n A)*(ballConstant n*weightMass n B)^p)^(1/(1-p*q)) / ballConstant n

lemma sourceConstant_pos {n : ℕ} (hn : 3 ≤ n) {p q A B : ℝ} (hA : -2 < A) (hB : -2 < B) :
    0 < sourceConstant n p q A B := by
  exact div_pos (Real.rpow_pos_of_pos
    (mul_pos (mul_pos (ballConstant_pos hn) (weightMass_pos hn hA))
      (Real.rpow_pos_of_pos (mul_pos (ballConstant_pos hn) (weightMass_pos hn hB)) p)) _)
    (ballConstant_pos hn)

lemma IsSolution.sourceMass_g_upper {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p) (hq : 0 < q)
    {R : ℝ} (hR : 0 < R) :
    sourceMass v p A R ≤ sourceConstant n p q A B * R^((n:ℝ)-2-alpha p q A B) := by
  have hn3 := h.dimension_ge_three hn
  have hA := h.first_weight_gt_neg_two hn
  have hB := h.swap.first_weight_gt_neg_two hn
  have hpq := h.product_gt_one hn hp hq
  let c := ballConstant n*weightMass n A
  let d := ballConstant n*weightMass n B
  have hc : 0 < c := mul_pos (ballConstant_pos hn3) (weightMass_pos hn3 hA)
  have hd : 0 < d := mul_pos (ballConstant_pos hn3) (weightMass_pos hn3 hB)
  have hu := coupled_upper_one (h.lowerMass_g_pos hn hR) (h.swap.lowerMass_g_pos hn hR)
    (mul_pos hc (Real.rpow_pos_of_pos hR (2+A)))
    (mul_pos hd (Real.rpow_pos_of_pos hR (2+B))) hp hpq
    (h.lowerMass_g_coupling hn hp hR) (h.swap.lowerMass_g_coupling hn hq hR)
  have hexp : (2+A+p*(2+B))*(1/(1-p*q)) = -alpha p q A B := by
    unfold alpha
    field_simp [ne_of_gt (show 0 < p*q-1 by linarith), ne_of_lt (show 1-p*q < 0 by linarith)]
    ring
  have he : ((c*R^(2+A))*(d*R^(2+B))^p)^(1/(1-p*q)) =
      (c*d^p)^(1/(1-p*q))*R^(-alpha p q A B) := by
    rw [Real.mul_rpow hd.le (Real.rpow_nonneg hR.le (2+B)),← Real.rpow_mul hR.le]
    have hinner : c*R^(2+A)*(d^p*R^((2+B)*p)) = c*d^p*R^(2+A+p*(2+B)) := by
      conv_rhs => rw [Real.rpow_add hR (2+A) (p*(2+B))]
      rw [mul_comm (2+B) p]; ring
    rw [hinner,Real.mul_rpow (mul_nonneg hc.le (Real.rpow_nonneg hd.le p))
      (Real.rpow_nonneg hR.le _),← Real.rpow_mul hR.le,hexp]
  rw [he,lowerMass_eq _ _ _ hR] at hu
  have hfactor : ballConstant n*R^(2-(n:ℝ)) *
      (sourceConstant n p q A B * R^((n:ℝ)-2-alpha p q A B)) =
      (c*d^p)^(1/(1-p*q))*R^(-alpha p q A B) := by
    unfold sourceConstant
    change ballConstant n*R^(2-(n:ℝ))*((c*d^p)^(1/(1-p*q))/ballConstant n * R^((n:ℝ)-2-alpha p q A B)) = _
    rw [show R^(-alpha p q A B) = R^(2-(n:ℝ))*R^((n:ℝ)-2-alpha p q A B) by
      rw [← Real.rpow_add hR]; congr 1; ring]
    field_simp [ne_of_gt (ballConstant_pos hn3)]
  rw [← hfactor] at hu
  exact (mul_le_mul_iff_right₀ (mul_pos (ballConstant_pos hn3) (Real.rpow_pos_of_pos hR _))).mp hu
end HenonLaneEmden

end
end MassGrowth

end OAI
